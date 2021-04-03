/* SPDX-License-Identifier: MIT */
/* Copyright © 2021 Max Bachmann */

#include <rapidfuzz/details/common.hpp>
#include <numeric>
#include <algorithm>
#include <array>
#include <limits>
#include <iostream>

namespace rapidfuzz {
namespace string_metric {
namespace detail {

/*
 * count the number of bits set in a 64 bit integer
 * The code uses wikipedia's 64-bit popcount implementation:
 * http://en.wikipedia.org/wiki/Hamming_weight#Efficient_implementation
 */
static inline std::size_t _popcount64(uint64_t x)
{
  const uint64_t m1  = 0x5555555555555555; //binary: 0101...
  const uint64_t m2  = 0x3333333333333333; //binary: 00110011..
  const uint64_t m4  = 0x0f0f0f0f0f0f0f0f; //binary:  4 zeros,  4 ones ...
  const uint64_t h01 = 0x0101010101010101; //the sum of 256 to the power of 0,1,2,3...

  x -= (x >> 1) & m1;             //put count of each 2 bits into those 2 bits
  x = (x & m2) + ((x >> 2) & m2); //put count of each 4 bits into those 4 bits
  x = (x + (x >> 4)) & m4;        //put count of each 8 bits into those 8 bits
  return static_cast<std::size_t>((x * h01) >> 56);  //returns left 8 bits of x + (x<<8) + (x<<16) + (x<<24) + ...
}

template <typename T, typename U>
constexpr T _bit_set(T val, U bit)
{
  return val | (1ull << bit);
}

template <typename T, typename U>
constexpr T _bit_check(T val, U bit)
{
  return (val >> bit) & 0x1;
}

static inline double jaro_calculate_similarity(size_t matches, size_t transpositions, size_t s1_len, size_t s2_len)
{
    transpositions /= 2;
    double similarity = matches / ((double) s1_len)
                      + matches / ((double) s2_len)
                      + ((double) (matches - transpositions)) / ((double) matches);
    return similarity / 3.0 * 100.0;
}

template <typename CharT1, typename CharT2>
static inline double jaro_similarity_impl(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
  assert(s1.size() <= 64);
  assert(s2.size() <= 64);

  if (s1.size() > s2.size()) {
    return jaro_similarity_impl(s2, s1);
  }

  /* this has to be handled here, since this would cause overflow issues in the implementation */
  if (s2.size() < 2) {
    return 0;
  }

  /* First, store the length of the strings
   * because the common prefix will be removed, but the similarity calculation
   * still requires the original length of the strings
   */
  const size_t s1_full_len = s1.size();
  const size_t s2_full_len = s2.size();

  // Initialize the counts for matches and transpositions.
  size_t matches = 0;        // no. of matched characters between s1 and s2
  size_t transpositions = 0; // no. of transpositions between s1 and s2

  /* remove common prefix and count it as matches */
  /* Suffix could be removed, but would lead to different transposition counts
   * AFAIK it would be <= the current one, which would probably be a good thing.
   * However it would lead to different results to the implementation this
   * is tested against, which is why it is not done yet.
   */
  matches = rapidfuzz::common::remove_common_prefix(s1, s2);

  /* s2 has s1 as prefix, so all matches and transpositions are known */
  if (s1.empty()) {
    return jaro_calculate_similarity(matches, transpositions, s1_full_len, s2_full_len);
  }

  const rapidfuzz::common::PatternMatchVector<sizeof(CharT2)> pattern(s2);
  uint64_t flagged_1 = 0; // positions in s1 which are matches to some character in s2
  uint64_t flagged_2 = 0; // positions in s2 which are matches to some character in s1

  /* The upper bound of the distance for being a matched character.
   * max(len_s1, len_s2)
   */
  const size_t match_bound = s2.size() / 2 - 1;

  auto match_character = [&](size_t s1_pos, uint64_t bound_mask) {
    uint64_t unused_matches = pattern.get(s1[s1_pos]) & ~flagged_2;

    unused_matches &= bound_mask;

    if (unused_matches) {
      const size_t s2_pos = __builtin_ctzll(unused_matches);
      flagged_1 = _bit_set(flagged_1, s1_pos);
      flagged_2 = _bit_set(flagged_2, s2_pos);
      matches++;
    }
  };

  /* Iterate through sequences, check for matches and compute transpositions.
   * jaro uses the following search range in s2:
   * - upperbound = min(s1_pos + match_bound, len_s2 - 1)
   * - lowerbound = max(0, s1_pos - match_bound)
   *
   *  The following implementation splits the iteration over s2 in sub ranges
   *  so this lower/upperbound does not has to be computed and applied to the
   *  bitvector in the inner loop
   */
  if (s1.size() <= match_bound) {
    /* upperbound is always len_s2 and lowerbound always 0, so it can be ignored */
    for (size_t s1_pos = 0; s1_pos < s1.size(); s1_pos++) {
      match_character(s1_pos, (uint64_t)-1);
    }
  } else {
    /* the iteration can be divided into three ranges, in which lower/upperbound
     * can be calculated without branches
     */
    size_t s1_pos = 0;
    uint64_t lowerbound_mask = (uint64_t)-1;
    uint64_t upperbound_mask = ((uint64_t)1 << match_bound) - 1;

    /* overlapping range left */
    for (; s1_pos <= match_bound; s1_pos++) {
      match_character(s1_pos, upperbound_mask);
      upperbound_mask = (upperbound_mask << 1) | 1;
    }

    lowerbound_mask <<= 1;

    /* overlapping range center (only exists for uneven string lengths)
     */
    if (s2.size() % 2) {
      match_character(s1_pos, lowerbound_mask & upperbound_mask);
      s1_pos++;
      lowerbound_mask <<= 1;
    }

    /* overlapping range right */
    for (; s1_pos < s1.size(); s1_pos++) {
      match_character(s1_pos, lowerbound_mask);
      lowerbound_mask <<= 1;
    }
  }

  /* If no characters in common - return */
  if (!matches) {
      return 0;
  }

  /* Count the number of transpositions */
  {
    size_t s2_pos = 0;
    for (size_t s1_pos = 0; s1_pos < s1.size(); s1_pos++) {
      if (_bit_check(flagged_1, s1_pos)) {
        if (!flagged_2) {
          if (s1[s1_pos] != s2.back()) {
            transpositions++;
          }
          continue;
        }

        const size_t index = __builtin_ctzll(flagged_2);

        if (s1[s1_pos] != s2[s2_pos + index]) {
          transpositions++;
        }

        flagged_2 >>= index + 1;
        s2_pos     += index + 1;
      }
    }
  }

  return jaro_calculate_similarity(matches, transpositions, s1_full_len, s2_full_len);
}

template <typename CharT1, typename CharT2>
static inline double jaro_similarity_impl_block(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
  if (!s1.size() || !s2.size()) {
    return 100 * static_cast<double>(!s1.size() && !s2.size());
  }

  if (s1.size() > s2.size()) {
    return jaro_similarity_impl_block(s2, s1);
  }

  // First, store the length of the strings
  // because the common prefix will be removed, but the similarity calculation
  // still requires the original length of the strings
  const size_t s1_full_len = s1.size();
  const size_t s2_full_len = s2.size();

  // Initialize the counts for matches and transpositions.
  size_t matches = 0;        // no. of matched characters between s1 and s2
  size_t transpositions = 0; // no. of transpositions between s1 and s2

  /* remove common prefix and count it as matches */
  /* TODO: test whether the suffix can be removed as well */
  matches = rapidfuzz::common::remove_common_prefix(s1, s2);

  /* s2 has s1 as prefix, so all matches and transpositions are known */
  if (s1.empty()) {
    return jaro_calculate_similarity(matches, transpositions, s1_full_len, s2_full_len);
  }

  /* positions have to be stored accross multiple computer words */
  const rapidfuzz::common::BlockPatternMatchVector<sizeof(CharT2)> pattern(s2);
  const std::size_t words1 = (s1.size() / 64) + (std::size_t)((s1.size() % 64) > 0);
  std::vector<uint64_t> flagged_1(words1); // positions in s1 which are matches to some character in s2
  const std::size_t words2 = pattern.m_val.size();
  std::vector<uint64_t> flagged_2(words2); // positions in s2 which are matches to some character in s1

  /* The upper bound of the distance for being a matched character.
   * max(len_s1, len_s2)
   */
  const size_t match_bound = s2.size() / 2 - 1;

  /* Iterate through sequences, check for matches and compute transpositions.
   * jaro uses the following search range in s2:
   * - upperbound = min(s1_pos + match_bound, len_s2 - 1)
   * - lowerbound = max(0, s1_pos - match_bound)
   *
   *  The following implementation splits the iteration over s2 in sub ranges
   *  so this lower/upperbound does not has to be computed and applied to the
   *  bitvector in the inner loop
   */
  if (s1.size() <= match_bound) {
    /* upperbound is always len_s2 and lowerbound always 0, so it can be ignored */
    for (size_t i = 0; i < s1.size(); i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;
      for (std::size_t word2 = 0; word2 < words2; word2++) {
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[word2] = _bit_set(flagged_2[word2], index);
          matches++;
          /* after word is found check next character */
          break;
        }
      }
    }
  } else {
    /* the iteration can be divided into two ranges, in which lower/upperbound
     * can be calculated without branches
     */
    /* overlapping range left */
    for (size_t i = 0; i <= match_bound; i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;

      /* clear non search range on the right */
      const size_t upperbound = i + match_bound;
      const size_t upperbound_words = upperbound / 64;
      const size_t upperbound_pos = upperbound % 64;

      /* upperbound only has to be cleared in the last word
       * it is guaranteed, that upperbound_words <= words2
       */
      for (std::size_t word2 = 0; word2 < upperbound_words; word2++) {
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[word2] = _bit_set(flagged_2[word2], index);
          matches++;
          /* after character is matched continue with the next */
          break;
        }
      }

      if (upperbound_pos) {
        // clear character positions in s2 which already match a character in s1
        const uint64_t unused_matches = pattern.get(upperbound_words, s1[i]) & ~flagged_2[upperbound_words];

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches);
          if (index <= upperbound_pos) {
            flagged_1[word1] = _bit_set(flagged_1[word1], i);
            flagged_2[upperbound_words] = _bit_set(flagged_2[upperbound_words], index);
            matches++;
          }
        }
      }
    }

    /* overlapping range right */
    for (size_t i = match_bound + 1; i < s1.size(); i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;

      /* clear non search range on the left */
      const size_t lowerbound = i - match_bound;
      const size_t lowerbound_words = lowerbound / 64;
      const size_t lowerbound_pos = lowerbound % 64;

      /* lowerbound only has to be cleared in the first word
       * it is guaranteed, that words2 > lowerbound_words
       */
      {
        /* clear character positions in s2 which already match a character in s1 */
        uint64_t unused_matches = pattern.get(lowerbound_words, s1[i]) & ~flagged_2[lowerbound_words];

        /* at most shift by 63 */
        unused_matches >>= lowerbound_pos;
        unused_matches <<= lowerbound_pos;

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[lowerbound_words] = _bit_set(flagged_2[lowerbound_words], index);
          matches++;
          /* after character is matched continue with the next */
          continue;
        }
      }

      for (std::size_t word2 = lowerbound_words + 1; word2 < words2; word2++) {
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[word2] = _bit_set(flagged_2[word2], index);
          matches++;
          /* todo potentially faster to have a counter in here instead of words1 * bitcount */
          /* after character is matched continue with the next */
          break;
        }
      }
    }
  }

  /* If no characters in common - return */
  if (!matches) {
    return 0;
  }

    /* Count the number of transpositions */
    /* todo this can definetly be done faster */
  {
    size_t k = 0;
    for (size_t i = 0; i < s1.size(); i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;
      if (_bit_check(flagged_1[word1], word1_pos)) {
        size_t j = k;
        for (; j < s2.size(); j++) {
          const uint64_t word2 = j / 64;
          const uint64_t word2_pos = j % 64;
          if (_bit_check(flagged_2[word2], word2_pos)) {
            k = j + 1;
            break;
          }
        }
        if (s1[i] != s2[j]) {
          transpositions++;
        }
      }
    }
  }

  return jaro_calculate_similarity(matches, transpositions, s1_full_len, s2_full_len);
}

template <typename CharT1, typename CharT2>
static inline double jaro_similarity(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
  if(s1.size() > 64 || s2.size() > 64) {
    return jaro_similarity_impl_block(s1, s2);
  }
  return jaro_similarity_impl(s1, s2);
}

} // namespace detail
} // namespace string_metric
} // namespace rapidfuzz

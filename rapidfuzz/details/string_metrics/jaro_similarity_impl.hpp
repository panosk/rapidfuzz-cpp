/* SPDX-License-Identifier: MIT */
/* Copyright © 2021 Max Bachmann */

#include <rapidfuzz/details/common.hpp>
#include <rapidfuzz/details/builtin.h>
#include <numeric>
#include <algorithm>
#include <array>
#include <limits>
#include <iostream>
#include <bitset>

#undef NDEBUG

namespace rapidfuzz {
namespace string_metric {
namespace detail {

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
  if (s1.empty() || s2.size() < 2) {
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

  /* remove common prefix and count it as matches. The common prefix can not
   * have any transpositions, so it is a lot faster to remove it beforehand
   */
  matches = rapidfuzz::common::remove_common_prefix(s1, s2);

  /* s2 has s1 as prefix, so all matches and transpositions are known */
  if (s1.empty()) {
    return jaro_calculate_similarity(matches, transpositions, s1_full_len, s2_full_len);
  }

  const rapidfuzz::common::PatternMatchVector<sizeof(CharT2)> pattern(s2);
  uint64_t flagged_1 = 0; // positions in s1 which are matches to some character in s2
  uint64_t flagged_2 = 0; // positions in s2 which are matches to some character in s1

  /* Iterate through sequences, check for matches and compute transpositions.
   * Two characters from s1 and s2 respectively, are considered matching only
   * if they are the same and not farther than `max(len_s1, len_s2) / 2 - 1`
   * characters apart.
   * In this implementation this is achieved using a bitmasks, to ignore
   * previous matches and characters outside of the search range.
   */

  /* The upper bound of the distance for being a matched character.
   * max(s1_full_len, s2_full_len). It is important to calculate the boundary using the 
   * string length before the common prefix is removed, so the length change
   * does not affect the search range.
   */
  const size_t match_bound = s2_full_len / 2 - 1;
  /* the bound mask starts as 1^(match_bound+1) to cover both the current element
   * and the match bound.
   */
  uint64_t bound_mask = ((uint64_t)1 << (match_bound+1)) - 1;

  size_t s1_pos = 0;
  /* for s1_pos < match_bound, the bitmask is shifted by one, setting the first bit to 1
   * to cover the match bound in both directions of s1_pos
   */
  const size_t range_left = std::min(s1.size(), match_bound);
  for(; s1_pos < range_left; s1_pos++) {
    uint64_t unused_matches = pattern.get(s1[s1_pos]) & ~flagged_2;
    unused_matches &= bound_mask;

    if (unused_matches) {
      const size_t s2_pos = psnip_builtin_ctz64(unused_matches);
      flagged_1 = _bit_set(flagged_1, s1_pos);
      flagged_2 = _bit_set(flagged_2, s2_pos);
      matches++;
    }

    bound_mask = (bound_mask << 1) | 1;
  }

  /* for s1_pos >= match_bound the bitmask is only shifted by one, since the first
   * character is now to far apart from s1_pos and should be ignored.
   * We can ignore, that the bitmask covers characters beyond s2_len,
   * since they do not exist in the PatternMatchVector
   */
  for(; s1_pos < s1.size(); s1_pos++) {
    uint64_t unused_matches = pattern.get(s1[s1_pos]) & ~flagged_2;
    unused_matches &= bound_mask;

    if (unused_matches) {
      const size_t s2_pos = psnip_builtin_ctz64(unused_matches);
      flagged_1 = _bit_set(flagged_1, s1_pos);
      flagged_2 = _bit_set(flagged_2, s2_pos);
      matches++;
    }

    bound_mask <<= 1;
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

        const size_t index = psnip_builtin_ctz64(flagged_2);

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


  auto match_character = [&s1, &flagged_2, &flagged_1, &pattern, &matches, words2](
    size_t word1, size_t word1_pos, size_t s1_pos,
    size_t lowerbound_words, uint64_t lowerbound_mask) __attribute__((always_inline))
  {
    {
      /* clear character positions in s2 which already match a character in s1 */
      uint64_t unused_matches = pattern.get(lowerbound_words, s1[s1_pos]) & ~flagged_2[lowerbound_words];

      unused_matches &= lowerbound_mask;

      if (unused_matches) {
        const int index = psnip_builtin_ctz64(unused_matches) ;
        flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
        flagged_2[lowerbound_words] = _bit_set(flagged_2[lowerbound_words], index);
        matches++;

        /* after character is matched continue with the next */
        return;
      }
    }

    for (std::size_t word2 = lowerbound_words + 1; word2 < words2; word2++) {
      /* clear character positions in s2 which already match a character in s1 */
      const uint64_t unused_matches = pattern.get(word2, s1[s1_pos]) & ~flagged_2[word2];

      if (unused_matches) {
        const int word2_pos = psnip_builtin_ctz64(unused_matches) ;
        flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
        flagged_2[word2] = _bit_set(flagged_2[word2], word2_pos);
        matches++;
        /* after character is matched continue with the next */
        break;
      }
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
    for (size_t i = 0; i < s1.size(); i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;
      for (std::size_t word2 = 0; word2 < words2; word2++) {
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

        if (unused_matches) {
          const int index = psnip_builtin_ctz64(unused_matches) ;
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


    //size_t upperbound_words = match_bound / 64;
    //uint64_t upperbound_mask = ((uint64_t)1 << (match_bound % 64)) - 1;

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
          const int index = psnip_builtin_ctz64(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[word2] = _bit_set(flagged_2[word2], index);
          matches++;
          /* after character is matched continue with the next */
          break;
        }
      }

      if (upperbound_pos) {
        // clear character positions in s2 which already match a character in s1
        uint64_t unused_matches = pattern.get(upperbound_words, s1[i]) & ~flagged_2[upperbound_words];

        //unused_matches &= upperbound_mask;

        if (unused_matches) {
          const int index = psnip_builtin_ctz64(unused_matches);
          if (index <= upperbound_pos) {
            flagged_1[word1] = _bit_set(flagged_1[word1], i);
            flagged_2[upperbound_words] = _bit_set(flagged_2[upperbound_words], index);
            matches++;
          }
        }
      }

      /*upperbound_mask = (upperbound_mask << 1) | 1;
      if(!(~upperbound_mask)) {
        upperbound_words++;
        upperbound_mask = 0;
      }*/
    }


    size_t lowerbound_words = 0;
    uint64_t lowerbound_mask = (uint64_t)-1 << 1;

    /* overlapping range right */
    for (size_t i = match_bound + 1; i < s1.size(); i++) {
      const uint64_t word1 = i / 64;
      const uint64_t word1_pos = i % 64;
#if 0
      match_character(word1, word1_pos, i, lowerbound_words, lowerbound_mask);

      lowerbound_mask <<= 1;
      if (!lowerbound_mask) {
        lowerbound_words++;
        lowerbound_mask = (uint64_t)-1;
      }
#else
      /* lowerbound only has to be cleared in the first word
       * it is guaranteed, that words2 > lowerbound_words
       */
      {
        /* clear character positions in s2 which already match a character in s1 */
        uint64_t unused_matches = pattern.get(lowerbound_words, s1[i]) & ~flagged_2[lowerbound_words];

        unused_matches &= lowerbound_mask;

        if (unused_matches) {
          const int index = psnip_builtin_ctz64(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[lowerbound_words] = _bit_set(flagged_2[lowerbound_words], index);
          matches++;

          lowerbound_mask <<= 1;
          if (!lowerbound_mask) {
            lowerbound_words++;
            lowerbound_mask = (uint64_t)-1;
          }

          /* after character is matched continue with the next */
          continue;
        }
      }

      for (std::size_t word2 = lowerbound_words + 1; word2 < words2; word2++) {
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

        if (unused_matches) {
          const int index = psnip_builtin_ctz64(unused_matches) ;
          flagged_1[word1] = _bit_set(flagged_1[word1], word1_pos);
          flagged_2[word2] = _bit_set(flagged_2[word2], index);
          matches++;
          /* after character is matched continue with the next */
          break;
        }
      }

      lowerbound_mask <<= 1;
      if (!lowerbound_mask) {
        lowerbound_words++;
        lowerbound_mask = (uint64_t)-1;
      }
#endif
    }
  }

  /* If no characters in common - return */
  if (!matches) {
    return 0;
  }
  return matches;

    /* Count the number of transpositions */
    /* todo this can definetly be done faster */
  {
    size_t k = 0;
    for (size_t s1_pos = 0; s1_pos < s1.size(); s1_pos++) {
      const uint64_t word1 = s1_pos / 64;
      const uint64_t word1_pos = s1_pos % 64;
      if (_bit_check(flagged_1[word1], word1_pos)) {
        size_t s2_pos = k;
        for (; s2_pos < s2.size(); s2_pos++) {
          const uint64_t word2 = s2_pos / 64;
          const uint64_t word2_pos = s2_pos % 64;
          if (_bit_check(flagged_2[word2], word2_pos)) {
            k = s2_pos + 1;
            break;
          }
        }
        if (s1[s1_pos] != s2[s2_pos]) {
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

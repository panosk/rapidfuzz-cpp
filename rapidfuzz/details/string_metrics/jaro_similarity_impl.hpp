/* SPDX-License-Identifier: MIT */
/* Copyright © 2021 Max Bachmann */

#include <rapidfuzz/details/common.hpp>
#include <numeric>
#include <algorithm>
#include <array>
#include <limits>


namespace rapidfuzz {
namespace string_metric {
namespace detail {


static inline double jaro_calculate_similarity(size_t matches, size_t transpositions, size_t s1_len, size_t s2_len)
{
    assert(matches != 0);
    transpositions /= 2;
    double similarity = matches / ((double) s1_len)
                      + matches / ((double) s2_len)
                      + ((double) (matches - transpositions)) / ((double) matches);
    return similarity / 3.0 * 100.0;
}

template <typename CharT1, typename CharT2>
double jaro_similarity_impl(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
    assert(s1.size() < 65);
    assert(s2.size() < 65);

    if (!s1.size() || !s2.size()) {
        return 100 * static_cast<double>(!s1.size() && !s2.size());
    }

    if (s1.size() > s2.size()) {
        return jaro_similarity(s2, s1);
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

    const rapidfuzz::common::PatternMatchVector<sizeof(CharT2)> pattern(s2);
    uint64_t flagged_1 = 0 // positions in s1 which are matches to some character in s2
    uint64_t flagged_2 = 0 // positions in s2 which are matches to some character in s1

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
        /* clear character positions in s2 which already match a character in s1 */
        const uint64_t unused_matches = pattern.get(s1[i]) & ~flagged_2;

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches) ;
          flagged_1 = bit_set(flagged_1, i);
          flagged_2 = bit_set(flagged_2, index);
        }
      }
    } else {
      /* the iteration can be divided into two ranges, in which lower/upperbound
       * can be calculated without branches
       */
      /* overlapping range left */
      for (size_t i = 0; i <= match_bound; i++) {
        // clear character positions in s2 which already match a character in s1
        const uint64_t unused_matches = pattern.get(s1[i]) & ~flagged_2;
        /* clear non search range on the right */
        const size_t upperbound = i + match_bound;

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches);
          if (index <= upperbound) {
            flagged_1 = bit_set(flagged_1, i);
            flagged_2 = bit_set(flagged_2, index);
          }
        }
      }

      /* overlapping range right */
      for (size_t i = match_bound + 1; i < s1.size(); i++) {
        /* clear character positions in s2 which already match a character in s1 */
        uint64_t unused_matches = pattern.get(s1[i]) & ~flagged_2;
        /* clear non search range on the left */
        const size_t lowerbound = i - match_bound;
        unused_matches >>= lowerbound;
        unused_matches <<= lowerbound;

        if (unused_matches) {
          const int index = __builtin_ctzll(unused_matches);
          flagged_1 = bit_set(flagged_1, i);
          flagged_2 = bit_set(flagged_2, index);
        }
      }
    }

    /* If no characters in common - return */
    if (!flagged_2 && !common_chars) {
        return 0;
    }

    /* count no. of matched characters by counting no. of
     * positions in s1 which are matches to some character in s2
     */
    matches += popcount64(flagged_1);

    /* Count the number of transpositions */
    {
      size_t k = 0;
      for (size_t i = 0; i < s1.size(); i++) {
        if (bit_check(flagged_1, i)) {
          size_t j = k;
          for (; j < s2.size(); j++) {
            if (bit_check(flagged_2, j)) {
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

  return jaro_calculate_similarity(common_chars, transpositions, s1_full_len, s2_full_len);
}

template <typename CharT1, typename CharT2>
double jaro_similarity_impl_block(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
    assert(s1.size() < 65);
    assert(s2.size() < 65);

    if (!s1.size() || !s2.size()) {
        return 100 * static_cast<double>(!s1.size() && !s2.size());
    }

    if (s1.size() > s2.size()) {
        return jaro_similarity(s2, s1);
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
            flagged_1[word1] = bit_set(flagged_1[word1], word1_pos);
            flagged_2[word2] = bit_set(flagged_2[word2], index);
            common_chars++;
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
        const size_t upperbound_words = words2;
        const size_t upperbound_pos = upperbound;

        /* the last computer word in s2 might not be full */
        const size_t last_word2_len = s2.size() % 64;
        if (upperbound >= last_word2_len) {
          upperbound_words -= 1;
          upperbound -= last_word2_len;
          upperbound_words -= upperbound / 64;
          upperbound_pos = upperbound % 64;
        }

        /* upperbound only has to be cleared in the last word
         * it is guaranteed, that upperbound_words <= words2
         */
        for (std::size_t word2 = 0; word2 < upperbound_words-1; word2++) {
          /* clear character positions in s2 which already match a character in s1 */
          const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

          if (unused_matches) {
            const int index = __builtin_ctzll(unused_matches) ;
            flagged_1[word1] = bit_set(flagged_1[word1], word1_pos);
            flagged_2[word2] = bit_set(flagged_2[word2], index);
            /* after character is matched continue with the next */
            break;
          }
        }

        {
          // clear character positions in s2 which already match a character in s1
          const uint64_t unused_matches = pattern.get(s1[i]) & ~flagged_2[upperbound_words-1];

          if (unused_matches) {
            const int index = __builtin_ctzll(unused_matches);
            if (index <= upperbound_pos) {
              flagged_1[word1] = bit_set(flagged_1[word1], i);
              flagged_2[upperbound_words-1] = bit_set(flagged_2[upperbound_words-1], index);
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
        const size_t lowerbound_words = upperbound / 64;
        const size_t lowerbound_pos = upperbound % 64;

        /* lowerbound only has to be cleared in the first word
         * it is guaranteed, that words2 > lowerbound_words
         */
        {
          /* clear character positions in s2 which already match a character in s1 */
          const uint64_t unused_matches = pattern.get(lowerbound_words, s1[i]) & ~flagged_2[lowerbound_words];

          /* at most shift by 63 */
          unused_matches >>= lowerbound_pos;
          unused_matches <<= lowerbound_pos;

          if (unused_matches) {
            const int index = __builtin_ctzll(unused_matches) ;
            flagged_1[word1] = bit_set(flagged_1[word1], word1_pos);
            flagged_2[lowerbound_words] = bit_set(flagged_2[lowerbound_words], index);
            common_chars++;
            /* after character is matched continue with the next */
            continue;
          }
        }

        for (std::size_t word2 = lowerbound_words + 1; word2 < words2; word2++) {
          /* clear character positions in s2 which already match a character in s1 */
          const uint64_t unused_matches = pattern.get(word2, s1[i]) & ~flagged_2[word2];

          if (unused_matches) {
            const int index = __builtin_ctzll(unused_matches) ;
            flagged_1[word1] = bit_set(flagged_1[word1], word1_pos);
            flagged_2[word2] = bit_set(flagged_2[word2], index);
            common_chars++;
            /* todo potentially faster to have a counter in here instead of words1 * bitcount */
            /* after character is matched continue with the next */
            break;
          }
        }
    }

    /* If no characters in common - return */
    if (!common_chars) {
        return 0;
    }

    /* Count the number of transpositions */
    /* todo this can definetly be done faster */
    {
      size_t k = 0;
      for (size_t i = 0; i < s1.size(); i++) {
        const uint64_t word1 = i / 64;
        const uint64_t word1_pos = i % 64;
        if (bit_check(flagged_1[word1], word1_pos)) {
          size_t j = k;
          for (; j < s2.size(); j++) {
            const uint64_t word2 = j / 64;
            const uint64_t word2_pos = j % 64;
            if (bit_check(flagged_2[word2], word2_pos)) {
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

  return jaro_calculate_similarity(common_chars, transpositions, s1_full_len, s2_full_len);
}



} // namespace detail
} // namespace string_metric
} // namespace rapidfuzz

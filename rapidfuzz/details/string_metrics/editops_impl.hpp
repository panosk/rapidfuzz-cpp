/* SPDX-License-Identifier: MIT */
/* Copyright © 2020 Max Bachmann */

#include <rapidfuzz/details/common.hpp>
#include <numeric>
#include <algorithm>
#include <array>
#include <limits>
#include <stdexcept>


namespace rapidfuzz {
namespace string_metric {
namespace detail {

template <typename CharT1, typename CharT2>
std::vector<std::size_t> levenshtein_matrix(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
  std::size_t rows = s1.size() + 1;
  std::size_t cols = s2.size() + 1;
  std::size_t matrix_size = rows * cols;
  if (matrix_size / rows != cols)
  {
    throw std::length_error("cannot create matrix larger than SIZE_MAX");
  }
  std::vector<std::size_t> matrix(rows * cols);

  for (std::size_t col = 0; col < cols; col++)
  {
    matrix[col] = col;
  }

  for (std::size_t row = 1; row < rows; row++)
  {
    matrix[row * cols] = row;
  }

  for (std::size_t i = 0; i < s1.size(); i++) {
    size_t* prev = &matrix[i * cols];
    size_t* cur = &matrix[(i + 1) * cols + 1];
    auto char1 = s1[i];
    size_t temp = i;

    for (const auto& char2 : s2) {
      temp = std::min({temp + 1, *prev + (char1 != char2), *(prev + 1) + 1});
      *cur = temp;
      cur++;
      prev++;
    }
  }

  return matrix;
}

template <typename CharT1, typename CharT2>
std::vector<LevenshteinEditOp> levenshtein_editops(basic_string_view<CharT1> s1, basic_string_view<CharT2> s2)
{
  /* prefix and suffix are no-ops, which do not need to be added to the editops */
  auto affix = common::remove_common_affix(s1, s2);
  std::vector<std::size_t> matrix = levenshtein_matrix(s1, s2);
  std::size_t dist = matrix.back();

  std::vector<LevenshteinEditOp> editops(dist);

  if (dist == 0)
  {
    return editops;
  }

  std::size_t row = s1.size();
  std::size_t col = s2.size();
  std::size_t cols = s2.size() + 1;
  const std::size_t* cur = &matrix.back();

  while (row || col)
  {
    LevenshteinEditType type;

    /* horizontal == current -> no-operation */
    if (row && col && (*cur == *(cur - cols - 1)))
    {
      row--;
      col--;
      cur -= cols + 1;
      continue;
    }
    /* horizontal == current + 1 -> replacement */
    else if (row && col && (*cur == *(cur - cols - 1) + 1))
    {
      dist--;
      editops[dist].type = LevenshteinEditType::Replace;
      editops[dist].src_pos = row + affix.prefix_len;
      editops[dist].dest_pos = col + affix.prefix_len;
      row--;
      col--;
      cur -= cols + 1;
    }
    /* left == current + 1 -> insertion */
    else if (row && (*cur == *(cur - 1) + 1))
    {
      dist--;
      editops[dist].type = LevenshteinEditType::Insert;
      editops[dist].src_pos = row + affix.prefix_len;
      editops[dist].dest_pos = col + affix.prefix_len;
      row--;
      cur -= cols + 1;
    }
    /* above == current + 1 -> deletion */
    else
    {
      /* this should be the case as long as there is no error in the implementation */
      assert((col && (*cur == *(cur - cols) + 1)));

      dist--;
      editops[dist].type = LevenshteinEditType::Delete;
      editops[dist].src_pos = row + affix.prefix_len;
      editops[dist].dest_pos = col + affix.prefix_len;
      row--;
      col--;
      cur -= cols + 1;
    }
  }

  return editops;
}

} // namespace detail
} // namespace levenshtein
} // namespace rapidfuzz
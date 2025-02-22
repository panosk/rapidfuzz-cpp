#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>
#include <string>

#include <rapidfuzz/distance/Indel.hpp>

TEST_CASE("Indel")
{
    std::string test = "aaaa";
    std::string replace_all = "bbbb";

    SECTION("similar strings")
    {
        REQUIRE(rapidfuzz::lcs_seq_distance(test, test) == 0);
        REQUIRE(rapidfuzz::lcs_seq_similarity(test, test) == 4);
        REQUIRE(rapidfuzz::lcs_seq_normalized_distance(test, test) == 0.0);
        REQUIRE(rapidfuzz::lcs_seq_normalized_similarity(test, test) == 1.0);
    }

    SECTION("completly different strings")
    {
        REQUIRE(rapidfuzz::lcs_seq_distance(test, replace_all) == 4);
        REQUIRE(rapidfuzz::lcs_seq_similarity(test, replace_all) == 0);
        REQUIRE(rapidfuzz::lcs_seq_normalized_distance(test, replace_all) == 1.0);
        REQUIRE(rapidfuzz::lcs_seq_normalized_similarity(test, replace_all) == 0.0);
    }

    SECTION("some tests for mbleven")
    {
        std::string a = "South Korea";
        std::string b = "North Korea";
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b) == 2);
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b, 4) == 2);
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b, 3) == 2);
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b, 2) == 2);
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b, 1) == 2);
        REQUIRE(rapidfuzz::lcs_seq_distance(a, b, 0) == 1);
    }
};

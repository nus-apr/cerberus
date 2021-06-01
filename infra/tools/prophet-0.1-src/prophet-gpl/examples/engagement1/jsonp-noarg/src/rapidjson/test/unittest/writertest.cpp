#include "unittest.h"
#include "rapidjson/reader.h"
#include "rapidjson/writer.h"
#include "rapidjson/stringbuffer.h"

using namespace rapidjson;

TEST(Writer, Compact) {
	StringStream s("{ \"hello\" : \"world\", \"t\" : true , \"f\" : false, \"n\": null, \"i\":123, \"pi\": 3.1416, \"a\":[1, 2, 3] } ");
	StringBuffer buffer;
	Writer<StringBuffer> writer(buffer);
	Reader reader;
	reader.Parse<0>(s, writer);
	EXPECT_STREQ("{\"hello\":\"world\",\"t\":true,\"f\":false,\"n\":null,\"i\":123,\"pi\":3.1416,\"a\":[1,2,3]}", buffer.GetString());
	EXPECT_EQ(77u, buffer.Size());
}

// json -> parse -> writer -> json
#define TEST_ROUNDTRIP(json) \
	{ \
		StringStream s(json); \
		StringBuffer buffer; \
		Writer<StringBuffer> writer(buffer); \
		Reader reader; \
		reader.Parse<0>(s, writer); \
		EXPECT_STREQ(json, buffer.GetString()); \
	}

TEST(Writer, Int) {
	TEST_ROUNDTRIP("[-1]");
	TEST_ROUNDTRIP("[-123]");
	TEST_ROUNDTRIP("[-2147483648]");
}

TEST(Writer, UInt) {
	TEST_ROUNDTRIP("[0]");
	TEST_ROUNDTRIP("[1]");
	TEST_ROUNDTRIP("[123]");
	TEST_ROUNDTRIP("[2147483647]");
	TEST_ROUNDTRIP("[4294967295]");
}

TEST(Writer, Int64) {
	TEST_ROUNDTRIP("[-1234567890123456789]");
	TEST_ROUNDTRIP("[-9223372036854775808]");
}

TEST(Writer, Uint64) {
	TEST_ROUNDTRIP("[1234567890123456789]");
	TEST_ROUNDTRIP("[9223372036854775807]");
}

TEST(Writer, String) {
	TEST_ROUNDTRIP("[\"Hello\"]");
	TEST_ROUNDTRIP("[\"Hello\\u0000World\"]");
	TEST_ROUNDTRIP("[\"\\\"\\\\/\\b\\f\\n\\r\\t\"]");
}

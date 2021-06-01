#include <string>
#include <stack>
#include <set>
#include <sstream>
#include <iostream>
#include <fstream>
#include "reader.h"
#include "document.h"
#include "rapidjson.h"
#include "filestream.h"
#include "internal/stack.h"
#include "internal/strfunc.h"
#include "prettywriter.h"

using namespace rapidjson;

template <class Stream, class Encoding,
	  typename Allocator = MemoryPoolAllocator<> >
class MyHandler: public rapidjson::BaseReaderHandler<Encoding>
{

public:

  typedef typename Encoding::Ch Ch;
  typedef uint16_t SizeType;

  MyHandler(Stream str, Allocator* allocator = 0,
	    size_t levelDepth = kDefaultLevelDepth):
    stream_(str),
    level_stack_(allocator, levelDepth * sizeof(Level))
  {}

  void String(const Ch* ch, SizeType siz, bool copy)
  {
    ProcessString(ch, siz);
  }

  void ProcessString(const Ch* str, SizeType length)
  {
    static const char hexDigits[] = "0123456789ABCDEF";
    static const char escape[256] = {
#define Z16 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
      //0 1 2 3 4 5 6 7 8 9 A B C D E F
      'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'b', 't', 'n', 'u', 'f', 'r', 'u', 'u', // 00
      'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', 'u', // 10
      0, 0, '"', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 20
      Z16, Z16, // 30~4F
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,'\\', 0, 0, 0, // 50
      Z16, Z16, Z16, Z16, Z16, Z16, Z16, Z16, Z16, Z16 // 60~FF
#undef Z16
    };

    std::stringstream stream;

    for (const Ch* p = str; p != str + length; ++p) {
      if ((sizeof(Ch) == 1 || *p < 256) && escape[(unsigned char)*p]) {
	stream << '\\';
	stream << escape[(unsigned char)*p];
	if (escape[(unsigned char)*p] == 'u') {
	  stream << '0';
	  stream << '0';
	  stream << '0';
	  stream << hexDigits[(*p) >> 4];
	  stream << hexDigits[(*p) & 0xF];
	}
      }
      else
	stream << *p;
    }

    if (m_keyStack.top().find(stream.str()) != m_keyStack.top().end())
      std::cout << stream.str() << "\n";

    m_keyStack.top().insert(stream.str());
  }

  void StartObject()
  {
    m_keyStack.push(KeySet());
  }

  void EndObject(SizeType length)
  {
    m_keyStack.pop();
  }

private:

  struct Level {
    Level(bool inArray_) : inArray(inArray_), valueCount(0) {}
    bool inArray; //!< true if in array, otherwise in object
    size_t valueCount; //!< number of values in this level
  };

  Stream& stream_;
  internal::Stack<Allocator> level_stack_;

  typedef std::set<std::string> KeySet;
  std::stack<KeySet> m_keyStack;

  static const size_t kDefaultLevelDepth = 32;
};

int main(int argc, char **argv)
{
  typedef rapidjson::UTF16<char> Encoding;
  //typedef rapidjson::UTF8<char> Encoding;

  FILE *infile = fopen(argv[1], "r");
  rapidjson::FileStream fstr(infile);

  Document docu;
  docu.ParseStream<0>(fstr);

  FileStream f(stdout);

  MyHandler<rapidjson::FileStream, Encoding> handler(f);

  docu.Accept(handler);
}

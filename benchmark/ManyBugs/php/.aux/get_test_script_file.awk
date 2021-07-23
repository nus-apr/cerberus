#!/usr/bin/awk -f

BEGIN { 
    count = 0;

    print "#ifdef DEF_AF_TESTS";
    print "char *get_test_script_file(int num) {";
    print "    switch (num) {"
}

{
    gsub(",", "", $0);
    printf("    case %d:\n", ++count);
    printf("        return %s;\n", $0);
}

END { 
    print "    default:"
    print "        printf(\"Cannot handle this script file number: %d\\n\", num);"
    print "        exit(1);"
    print "    }"
    print "}";
    print "#endif";
}

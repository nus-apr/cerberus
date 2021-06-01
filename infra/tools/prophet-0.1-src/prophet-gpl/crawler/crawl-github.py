#!/usr/bin/env python
from urllib2 import urlopen
from bs4 import BeautifulSoup


def fetchProjectList(lang, date, page):
    ret = []
    url_str = "https://github.com/search?q=created%3A<" + date + \
              "&type=Repositories&ref=advsearch&l=" + lang + "&p=" + str(page)
    soup = BeautifulSoup(urlopen(url_str))

    # The hacky pattern is that the user_name/project_name will appear three
    # times in a row, and the last time starts with "/". It might be invalid
    # if github updates its webpage layout
    lastlink1 = ""
    lastlink2 = ""
    for link in soup.find_all('a'):
        linkstr = link.get('href')
        if (len(lastlink1) >= len(linkstr)) and \
           (len(lastlink2) >= len(linkstr)):
            if linkstr[0] == "/":
                if lastlink1[0:len(linkstr)-1] == linkstr[1:len(linkstr)]:
                    if lastlink2[0:len(linkstr)-1] == linkstr[1:len(linkstr)]:
                        if linkstr != "/":
                            ret.append(linkstr)
        lastlink2 = lastlink1
        lastlink1 = linkstr
    return ret

print fetchProjectList("C", "2011-01-01", "1")

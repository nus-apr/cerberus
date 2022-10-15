/*numPass=0, numTotal=5
Verdict:WRONG_ANSWER, Visibility:1, Input:"3 2", ExpOutput:"ab
ac
bc
", Output:"a
b
a
c
b
c
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"4 3", ExpOutput:"abc
abd
acd
bcd
", Output:"a
b
c
a
b
d
a
c
d
b
c
d
"
Verdict:WRONG_ANSWER, Visibility:1, Input:"5 3", ExpOutput:"abc
abd
abe
acd
ace
ade
bcd
bce
bde
cde
", Output:"a
b
c
a
b
d
a
b
e
a
c
d
a
c
e
a
d
e
b
c
d
b
c
e
b
d
e
c
d
e
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"10 5", ExpOutput:"abcde
abcdf
abcdg
abcdh
abcdi
abcdj
abcef
abceg
abceh
abcei
abcej
abcfg
abcfh
abcfi
abcfj
abcgh
abcgi
abcgj
abchi
abchj
abcij
abdef
abdeg
abdeh
abdei
abdej
abdfg
abdfh
abdfi
abdfj
abdgh
abdgi
abdgj
abdhi
abdhj
abdij
abefg
abefh
abefi
abefj
abegh
abegi
abegj
abehi
abehj
abeij
abfgh
abfgi
abfgj
abfhi
abfhj
abfij
abghi
abghj
abgij
abhij
acdef
acdeg
acdeh
acdei
acdej
acdfg
acdfh
acdfi
acdfj
acdgh
acdgi
acdgj
acdhi
acdhj
acdij
acefg
acefh
acefi
acefj
acegh
acegi
acegj
acehi
acehj
aceij
acfgh
acfgi
acfgj
acfhi
acfhj
acfij
acghi
acghj
acgij
achij
adefg
adefh
adefi
adefj
adegh
adegi
adegj
adehi
adehj
adeij
adfgh
adfgi
adfgj
adfhi
adfhj
adfij
adghi
adghj
adgij
adhij
aefgh
aefgi
aefgj
aefhi
aefhj
aefij
aeghi
aeghj
aegij
aehij
afghi
afghj
afgij
afhij
aghij
bcdef
bcdeg
bcdeh
bcdei
bcdej
bcdfg
bcdfh
bcdfi
bcdfj
bcdgh
bcdgi
bcdgj
bcdhi
bcdhj
bcdij
bcefg
bcefh
bcefi
bcefj
bcegh
bcegi
bcegj
bcehi
bcehj
bceij
bcfgh
bcfgi
bcfgj
bcfhi
bcfhj
bcfij
bcghi
bcghj
bcgij
bchij
bdefg
bdefh
bdefi
bdefj
bdegh
bdegi
bdegj
bdehi
bdehj
bdeij
bdfgh
bdfgi
bdfgj
bdfhi
bdfhj
bdfij
bdghi
bdghj
bdgij
bdhij
befgh
befgi
befgj
befhi
befhj
befij
beghi
beghj
begij
behij
bfghi
bfghj
bfgij
bfhij
bghij
cdefg
cdefh
cdefi
cdefj
cdegh
cdegi
cdegj
cdehi
cdehj
cdeij
cdfgh
cdfgi
cdfgj
cdfhi
cdfhj
cdfij
cdghi
cdghj
cdgij
cdhij
cefgh
cefgi
cefgj
cefhi
cefhj
cefij
ceghi
ceghj
cegij
cehij
cfghi
cfghj
cfgij
cfhij
cghij
defgh
defgi
defgj
defhi
defhj
defij
deghi
deghj
degij
dehij
dfghi
dfghj
dfgij
dfhij
dghij
efghi
efghj
efgij
efhij
eghij
fghij
", Output:"a
b
c
d
e
a
b
c
d
f
a
b
c
d
g
a
b
c
d
h
a
b
c
d
i
a
b
c
d
j
a
b
c
e
f
a
b
c
e
g
a
b
c
e
h
a
b
c
e
i
a
b
c
e
j
a
b
c
f
g
a
b
c
f
h
a
b
c
f
i
a
b
c
f
j
a
b
c
g
h
a
b
c
g
i
a
b
c
g
j
a
b
c
h
i
a
b
c
h
j
a
b
c
i
j
a
b
d
e
f
a
b
d
e
g
a
b
d
e
h
a
b
d
e
i
a
b
d
e
j
a
b
d
f
g
a
b
d
f
h
a
b
d
f
i
a
b
d
f
j
a
b
d
g
h
a
b
d
g
i
a
b
d
g
j
a
b
d
h
i
a
b
d
h
j
a
b
d
i
j
a
b
e
f
g
a
b
e
f
h
a
b
e
f
i
a
b
e
f
j
a
b
e
g
h
a
b
e
g
i
a
b
e
g
j
a
b
e
h
i
a
b
e
h
j
a
b
e
i
j
a
b
f
g
h
a
b
f
g
i
a
b
f
g
j
a
b
f
h
i
a
b
f
h
j
a
b
f
i
j
a
b
g
h
i
a
b
g
h
j
a
b
g
i
j
a
b
h
i
j
a
c
d
e
f
a
c
d
e
g
a
c
d
e
h
a
c
d
e
i
a
c
d
e
j
a
c
d
f
g
a
c
d
f
h
a
c
d
f
i
a
c
d
f
j
a
c
d
g
h
a
c
d
g
i
a
c
d
g
j
a
c
d
h
i
a
c
d
h
j
a
c
d
i
j
a
c
e
f
g
a
c
e
f
h
a
c
e
f
i
a
c
e
f
j
a
c
e
g
h
a
c
e
g
i
a
c
e
g
j
a
c
e
h
i
a
c
e
h
j
a
c
e
i
j
a
c
f
g
h
a
c
f
g
i
a
c
f
g
j
a
c
f
h
i
a
c
f
h
j
a
c
f
i
j
a
c
g
h
i
a
c
g
h
j
a
c
g
i
j
a
c
h
i
j
a
d
e
f
g
a
d
e
f
h
a
d
e
f
i
a
d
e
f
j
a
d
e
g
h
a
d
e
g
i
a
d
e
g
j
a
d
e
h
i
a
d
e
h
j
a
d
e
i
j
a
d
f
g
h
a
d
f
g
i
a
d
f
g
j
a
d
f
h
i
a
d
f
h
j
a
d
f
i
j
a
d
g
h
i
a
d
g
h
j
a
d
g
i
j
a
d
h
i
j
a
e
f
g
h
a
e
f
g
i
a
e
f
g
j
a
e
f
h
i
a
e
f
h
j
a
e
f
i
j
a
e
g
h
i
a
e
g
h
j
a
e
g
i
j
a
e
h
i
j
a
f
g
h
i
a
f
g
h
j
a
f
g
i
j
a
f
h
i
j
a
g
h
i
j
b
c
d
e
f
b
c
d
e
g
b
c
d
e
h
b
c
d
e
i
b
c
d
e
j
b
c
d
f
g
b
c
d
f
h
b
c
d
f
i
b
c
d
f
j
b
c
d
g
h
b
c
d
g
i
b
c
d
g
j
b
c
d
h
i
b
c
d
h
j
b
c
d
i
j
b
c
e
f
g
b
c
e
f
h
b
c
e
f
i
b
c
e
f
j
b
c
e
g
h
b
c
e
g
i
b
c
e
g
j
b
c
e
h
i
b
c
e
h
j
b
c
e
i
j
b
c
f
g
h
b
c
f
g
i
b
c
f
g
j
b
c
f
h
i
b
c
f
h
j
b
c
f
i
j
b
c
g
h
i
b
c
g
h
j
b
c
g
i
j
b
c
h
i
j
b
d
e
f
g
b
d
e
f
h
b
d
e
f
i
b
d
e
f
j
b
d
e
g
h
b
d
e
g
i
b
d
e
g
j
b
d
e
h
i
b
d
e
h
j
b
d
e
i
j
b
d
f
g
h
b
d
f
g
i
b
d
f
g
j
b
d
f
h
i
b
d
f
h
j
b
d
f
i
j
b
d
g
h
i
b
d
g
h
j
b
d
g
i
j
b
d
h
i
j
b
e
f
g
h
b
e
f
g
i
b
e
f
g
j
b
e
f
h
i
b
e
f
h
j
b
e
f
i
j
b
e
g
h
i
b
e
g
h
j
b
e
g
i
j
b
e
h
i
j
b
f
g
h
i
b
f
g
h
j
b
f
g
i
j
b
f
h
i
j
b
g
h
i
j
c
d
e
f
g
c
d
e
f
h
c
d
e
f
i
c
d
e
f
j
c
d
e
g
h
c
d
e
g
i
c
d
e
g
j
c
d
e
h
i
c
d
e
h
j
c
d
e
i
j
c
d
f
g
h
c
d
f
g
i
c
d
f
g
j
c
d
f
h
i
c
d
f
h
j
c
d
f
i
j
c
d
g
h
i
c
d
g
h
j
c
d
g
i
j
c
d
h
i
j
c
e
f
g
h
c
e
f
g
i
c
e
f
g
j
c
e
f
h
i
c
e
f
h
j
c
e
f
i
j
c
e
g
h
i
c
e
g
h
j
c
e
g
i
j
c
e
h
i
j
c
f
g
h
i
c
f
g
h
j
c
f
g
i
j
c
f
h
i
j
c
g
h
i
j
d
e
f
g
h
d
e
f
g
i
d
e
f
g
j
d
e
f
h
i
d
e
f
h
j
d
e
f
i
j
d
e
g
h
i
d
e
g
h
j
d
e
g
i
j
d
e
h
i
j
d
f
g
h
i
d
f
g
h
j
d
f
g
i
j
d
f
h
i
j
d
g
h
i
j
e
f
g
h
i
e
f
g
h
j
e
f
g
i
j
e
f
h
i
j
e
g
h
i
j
f
g
h
i
j
"
Verdict:WRONG_ANSWER, Visibility:0, Input:"12 7", ExpOutput:"abcdefg
abcdefh
abcdefi
abcdefj
abcdefk
abcdefl
abcdegh
abcdegi
abcdegj
abcdegk
abcdegl
abcdehi
abcdehj
abcdehk
abcdehl
abcdeij
abcdeik
abcdeil
abcdejk
abcdejl
abcdekl
abcdfgh
abcdfgi
abcdfgj
abcdfgk
abcdfgl
abcdfhi
abcdfhj
abcdfhk
abcdfhl
abcdfij
abcdfik
abcdfil
abcdfjk
abcdfjl
abcdfkl
abcdghi
abcdghj
abcdghk
abcdghl
abcdgij
abcdgik
abcdgil
abcdgjk
abcdgjl
abcdgkl
abcdhij
abcdhik
abcdhil
abcdhjk
abcdhjl
abcdhkl
abcdijk
abcdijl
abcdikl
abcdjkl
abcefgh
abcefgi
abcefgj
abcefgk
abcefgl
abcefhi
abcefhj
abcefhk
abcefhl
abcefij
abcefik
abcefil
abcefjk
abcefjl
abcefkl
abceghi
abceghj
abceghk
abceghl
abcegij
abcegik
abcegil
abcegjk
abcegjl
abcegkl
abcehij
abcehik
abcehil
abcehjk
abcehjl
abcehkl
abceijk
abceijl
abceikl
abcejkl
abcfghi
abcfghj
abcfghk
abcfghl
abcfgij
abcfgik
abcfgil
abcfgjk
abcfgjl
abcfgkl
abcfhij
abcfhik
abcfhil
abcfhjk
abcfhjl
abcfhkl
abcfijk
abcfijl
abcfikl
abcfjkl
abcghij
abcghik
abcghil
abcghjk
abcghjl
abcghkl
abcgijk
abcgijl
abcgikl
abcgjkl
abchijk
abchijl
abchikl
abchjkl
abcijkl
abdefgh
abdefgi
abdefgj
abdefgk
abdefgl
abdefhi
abdefhj
abdefhk
abdefhl
abdefij
abdefik
abdefil
abdefjk
abdefjl
abdefkl
abdeghi
abdeghj
abdeghk
abdeghl
abdegij
abdegik
abdegil
abdegjk
abdegjl
abdegkl
abdehij
abdehik
abdehil
abdehjk
abdehjl
abdehkl
abdeijk
abdeijl
abdeikl
abdejkl
abdfghi
abdfghj
abdfghk
abdfghl
abdfgij
abdfgik
abdfgil
abdfgjk
abdfgjl
abdfgkl
abdfhij
abdfhik
abdfhil
abdfhjk
abdfhjl
abdfhkl
abdfijk
abdfijl
abdfikl
abdfjkl
abdghij
abdghik
abdghil
abdghjk
abdghjl
abdghkl
abdgijk
abdgijl
abdgikl
abdgjkl
abdhijk
abdhijl
abdhikl
abdhjkl
abdijkl
abefghi
abefghj
abefghk
abefghl
abefgij
abefgik
abefgil
abefgjk
abefgjl
abefgkl
abefhij
abefhik
abefhil
abefhjk
abefhjl
abefhkl
abefijk
abefijl
abefikl
abefjkl
abeghij
abeghik
abeghil
abeghjk
abeghjl
abeghkl
abegijk
abegijl
abegikl
abegjkl
abehijk
abehijl
abehikl
abehjkl
abeijkl
abfghij
abfghik
abfghil
abfghjk
abfghjl
abfghkl
abfgijk
abfgijl
abfgikl
abfgjkl
abfhijk
abfhijl
abfhikl
abfhjkl
abfijkl
abghijk
abghijl
abghikl
abghjkl
abgijkl
abhijkl
acdefgh
acdefgi
acdefgj
acdefgk
acdefgl
acdefhi
acdefhj
acdefhk
acdefhl
acdefij
acdefik
acdefil
acdefjk
acdefjl
acdefkl
acdeghi
acdeghj
acdeghk
acdeghl
acdegij
acdegik
acdegil
acdegjk
acdegjl
acdegkl
acdehij
acdehik
acdehil
acdehjk
acdehjl
acdehkl
acdeijk
acdeijl
acdeikl
acdejkl
acdfghi
acdfghj
acdfghk
acdfghl
acdfgij
acdfgik
acdfgil
acdfgjk
acdfgjl
acdfgkl
acdfhij
acdfhik
acdfhil
acdfhjk
acdfhjl
acdfhkl
acdfijk
acdfijl
acdfikl
acdfjkl
acdghij
acdghik
acdghil
acdghjk
acdghjl
acdghkl
acdgijk
acdgijl
acdgikl
acdgjkl
acdhijk
acdhijl
acdhikl
acdhjkl
acdijkl
acefghi
acefghj
acefghk
acefghl
acefgij
acefgik
acefgil
acefgjk
acefgjl
acefgkl
acefhij
acefhik
acefhil
acefhjk
acefhjl
acefhkl
acefijk
acefijl
acefikl
acefjkl
aceghij
aceghik
aceghil
aceghjk
aceghjl
aceghkl
acegijk
acegijl
acegikl
acegjkl
acehijk
acehijl
acehikl
acehjkl
aceijkl
acfghij
acfghik
acfghil
acfghjk
acfghjl
acfghkl
acfgijk
acfgijl
acfgikl
acfgjkl
acfhijk
acfhijl
acfhikl
acfhjkl
acfijkl
acghijk
acghijl
acghikl
acghjkl
acgijkl
achijkl
adefghi
adefghj
adefghk
adefghl
adefgij
adefgik
adefgil
adefgjk
adefgjl
adefgkl
adefhij
adefhik
adefhil
adefhjk
adefhjl
adefhkl
adefijk
adefijl
adefikl
adefjkl
adeghij
adeghik
adeghil
adeghjk
adeghjl
adeghkl
adegijk
adegijl
adegikl
adegjkl
adehijk
adehijl
adehikl
adehjkl
adeijkl
adfghij
adfghik
adfghil
adfghjk
adfghjl
adfghkl
adfgijk
adfgijl
adfgikl
adfgjkl
adfhijk
adfhijl
adfhikl
adfhjkl
adfijkl
adghijk
adghijl
adghikl
adghjkl
adgijkl
adhijkl
aefghij
aefghik
aefghil
aefghjk
aefghjl
aefghkl
aefgijk
aefgijl
aefgikl
aefgjkl
aefhijk
aefhijl
aefhikl
aefhjkl
aefijkl
aeghijk
aeghijl
aeghikl
aeghjkl
aegijkl
aehijkl
afghijk
afghijl
afghikl
afghjkl
afgijkl
afhijkl
aghijkl
bcdefgh
bcdefgi
bcdefgj
bcdefgk
bcdefgl
bcdefhi
bcdefhj
bcdefhk
bcdefhl
bcdefij
bcdefik
bcdefil
bcdefjk
bcdefjl
bcdefkl
bcdeghi
bcdeghj
bcdeghk
bcdeghl
bcdegij
bcdegik
bcdegil
bcdegjk
bcdegjl
bcdegkl
bcdehij
bcdehik
bcdehil
bcdehjk
bcdehjl
bcdehkl
bcdeijk
bcdeijl
bcdeikl
bcdejkl
bcdfghi
bcdfghj
bcdfghk
bcdfghl
bcdfgij
bcdfgik
bcdfgil
bcdfgjk
bcdfgjl
bcdfgkl
bcdfhij
bcdfhik
bcdfhil
bcdfhjk
bcdfhjl
bcdfhkl
bcdfijk
bcdfijl
bcdfikl
bcdfjkl
bcdghij
bcdghik
bcdghil
bcdghjk
bcdghjl
bcdghkl
bcdgijk
bcdgijl
bcdgikl
bcdgjkl
bcdhijk
bcdhijl
bcdhikl
bcdhjkl
bcdijkl
bcefghi
bcefghj
bcefghk
bcefghl
bcefgij
bcefgik
bcefgil
bcefgjk
bcefgjl
bcefgkl
bcefhij
bcefhik
bcefhil
bcefhjk
bcefhjl
bcefhkl
bcefijk
bcefijl
bcefikl
bcefjkl
bceghij
bceghik
bceghil
bceghjk
bceghjl
bceghkl
bcegijk
bcegijl
bcegikl
bcegjkl
bcehijk
bcehijl
bcehikl
bcehjkl
bceijkl
bcfghij
bcfghik
bcfghil
bcfghjk
bcfghjl
bcfghkl
bcfgijk
bcfgijl
bcfgikl
bcfgjkl
bcfhijk
bcfhijl
bcfhikl
bcfhjkl
bcfijkl
bcghijk
bcghijl
bcghikl
bcghjkl
bcgijkl
bchijkl
bdefghi
bdefghj
bdefghk
bdefghl
bdefgij
bdefgik
bdefgil
bdefgjk
bdefgjl
bdefgkl
bdefhij
bdefhik
bdefhil
bdefhjk
bdefhjl
bdefhkl
bdefijk
bdefijl
bdefikl
bdefjkl
bdeghij
bdeghik
bdeghil
bdeghjk
bdeghjl
bdeghkl
bdegijk
bdegijl
bdegikl
bdegjkl
bdehijk
bdehijl
bdehikl
bdehjkl
bdeijkl
bdfghij
bdfghik
bdfghil
bdfghjk
bdfghjl
bdfghkl
bdfgijk
bdfgijl
bdfgikl
bdfgjkl
bdfhijk
bdfhijl
bdfhikl
bdfhjkl
bdfijkl
bdghijk
bdghijl
bdghikl
bdghjkl
bdgijkl
bdhijkl
befghij
befghik
befghil
befghjk
befghjl
befghkl
befgijk
befgijl
befgikl
befgjkl
befhijk
befhijl
befhikl
befhjkl
befijkl
beghijk
beghijl
beghikl
beghjkl
begijkl
behijkl
bfghijk
bfghijl
bfghikl
bfghjkl
bfgijkl
bfhijkl
bghijkl
cdefghi
cdefghj
cdefghk
cdefghl
cdefgij
cdefgik
cdefgil
cdefgjk
cdefgjl
cdefgkl
cdefhij
cdefhik
cdefhil
cdefhjk
cdefhjl
cdefhkl
cdefijk
cdefijl
cdefikl
cdefjkl
cdeghij
cdeghik
cdeghil
cdeghjk
cdeghjl
cdeghkl
cdegijk
cdegijl
cdegikl
cdegjkl
cdehijk
cdehijl
cdehikl
cdehjkl
cdeijkl
cdfghij
cdfghik
cdfghil
cdfghjk
cdfghjl
cdfghkl
cdfgijk
cdfgijl
cdfgikl
cdfgjkl
cdfhijk
cdfhijl
cdfhikl
cdfhjkl
cdfijkl
cdghijk
cdghijl
cdghikl
cdghjkl
cdgijkl
cdhijkl
cefghij
cefghik
cefghil
cefghjk
cefghjl
cefghkl
cefgijk
cefgijl
cefgikl
cefgjkl
cefhijk
cefhijl
cefhikl
cefhjkl
cefijkl
ceghijk
ceghijl
ceghikl
ceghjkl
cegijkl
cehijkl
cfghijk
cfghijl
cfghikl
cfghjkl
cfgijkl
cfhijkl
cghijkl
defghij
defghik
defghil
defghjk
defghjl
defghkl
defgijk
defgijl
defgikl
defgjkl
defhijk
defhijl
defhikl
defhjkl
defijkl
deghijk
deghijl
deghikl
deghjkl
degijkl
dehijkl
dfghijk
dfghijl
dfghikl
dfghjkl
dfgijkl
dfhijkl
dghijkl
efghijk
efghijl
efghikl
efghjkl
efgijkl
efhijkl
eghijkl
fghijkl
", Output:"a
b
c
d
e
f
g
a
b
c
d
e
f
h
a
b
c
d
e
f
i
a
b
c
d
e
f
j
a
b
c
d
e
f
k
a
b
c
d
e
f
l
a
b
c
d
e
g
h
a
b
c
d
e
g
i
a
b
c
d
e
g
j
a
b
c
d
e
g
k
a
b
c
d
e
g
l
a
b
c
d
e
h
i
a
b
c
d
e
h
j
a
b
c
d
e
h
k
a
b
c
d
e
h
l
a
b
c
d
e
i
j
a
b
c
d
e
i
k
a
b
c
d
e
i
l
a
b
c
d
e
j
k
a
b
c
d
e
j
l
a
b
c
d
e
k
l
a
b
c
d
f
g
h
a
b
c
d
f
g
i
a
b
c
d
f
g
j
a
b
c
d
f
g
k
a
b
c
d
f
g
l
a
b
c
d
f
h
i
a
b
c
d
f
h
j
a
b
c
d
f
h
k
a
b
c
d
f
h
l
a
b
c
d
f
i
j
a
b
c
d
f
i
k
a
b
c
d
f
i
l
a
b
c
d
f
j
k
a
b
c
d
f
j
l
a
b
c
d
f
k
l
a
b
c
d
g
h
i
a
b
c
d
g
h
j
a
b
c
d
g
h
k
a
b
c
d
g
h
l
a
b
c
d
g
i
j
a
b
c
d
g
i
k
a
b
c
d
g
i
l
a
b
c
d
g
j
k
a
b
c
d
g
j
l
a
b
c
d
g
k
l
a
b
c
d
h
i
j
a
b
c
d
h
i
k
a
b
c
d
h
i
l
a
b
c
d
h
j
k
a
b
c
d
h
j
l
a
b
c
d
h
k
l
a
b
c
d
i
j
k
a
b
c
d
i
j
l
a
b
c
d
i
k
l
a
b
c
d
j
k
l
a
b
c
e
f
g
h
a
b
c
e
f
g
i
a
b
c
e
f
g
j
a
b
c
e
f
g
k
a
b
c
e
f
g
l
a
b
c
e
f
h
i
a
b
c
e
f
h
j
a
b
c
e
f
h
k
a
b
c
e
f
h
l
a
b
c
e
f
i
j
a
b
c
e
f
i
k
a
b
c
e
f
i
l
a
b
c
e
f
j
k
a
b
c
e
f
j
l
a
b
c
e
f
k
l
a
b
c
e
g
h
i
a
b
c
e
g
h
j
a
b
c
e
g
h
k
a
b
c
e
g
h
l
a
b
c
e
g
i
j
a
b
c
e
g
i
k
a
b
c
e
g
i
l
a
b
c
e
g
j
k
a
b
c
e
g
j
l
a
b
c
e
g
k
l
a
b
c
e
h
i
j
a
b
c
e
h
i
k
a
b
c
e
h
i
l
a
b
c
e
h
j
k
a
b
c
e
h
j
l
a
b
c
e
h
k
l
a
b
c
e
i
j
k
a
b
c
e
i
j
l
a
b
c
e
i
k
l
a
b
c
e
j
k
l
a
b
c
f
g
h
i
a
b
c
f
g
h
j
a
b
c
f
g
h
k
a
b
c
f
g
h
l
a
b
c
f
g
i
j
a
b
c
f
g
i
k
a
b
c
f
g
i
l
a
b
c
f
g
j
k
a
b
c
f
g
j
l
a
b
c
f
g
k
l
a
b
c
f
h
i
j
a
b
c
f
h
i
k
a
b
c
f
h
i
l
a
b
c
f
h
j
k
a
b
c
f
h
j
l
a
b
c
f
h
k
l
a
b
c
f
i
j
k
a
b
c
f
i
j
l
a
b
c
f
i
k
l
a
b
c
f
j
k
l
a
b
c
g
h
i
j
a
b
c
g
h
i
k
a
b
c
g
h
i
l
a
b
c
g
h
j
k
a
b
c
g
h
j
l
a
b
c
g
h
k
l
a
b
c
g
i
j
k
a
b
c
g
i
j
l
a
b
c
g
i
k
l
a
b
c
g
j
k
l
a
b
c
h
i
j
k
a
b
c
h
i
j
l
a
b
c
h
i
k
l
a
b
c
h
j
k
l
a
b
c
i
j
k
l
a
b
d
e
f
g
h
a
b
d
e
f
g
i
a
b
d
e
f
g
j
a
b
d
e
f
g
k
a
b
d
e
f
g
l
a
b
d
e
f
h
i
a
b
d
e
f
h
j
a
b
d
e
f
h
k
a
b
d
e
f
h
l
a
b
d
e
f
i
j
a
b
d
e
f
i
k
a
b
d
e
f
i
l
a
b
d
e
f
j
k
a
b
d
e
f
j
l
a
b
d
e
f
k
l
a
b
d
e
g
h
i
a
b
d
e
g
h
j
a
b
d
e
g
h
k
a
b
d
e
g
h
l
a
b
d
e
g
i
j
a
b
d
e
g
i
k
a
b
d
e
g
i
l
a
b
d
e
g
j
k
a
b
d
e
g
j
l
a
b
d
e
g
k
l
a
b
d
e
h
i
j
a
b
d
e
h
i
k
a
b
d
e
h
i
l
a
b
d
e
h
j
k
a
b
d
e
h
j
l
a
b
d
e
h
k
l
a
b
d
e
i
j
k
a
b
d
e
i
j
l
a
b
d
e
i
k
l
a
b
d
e
j
k
l
a
b
d
f
g
h
i
a
b
d
f
g
h
j
a
b
d
f
g
h
k
a
b
d
f
g
h
l
a
b
d
f
g
i
j
a
b
d
f
g
i
k
a
b
d
f
g
i
l
a
b
d
f
g
j
k
a
b
d
f
g
j
l
a
b
d
f
g
k
l
a
b
d
f
h
i
j
a
b
d
f
h
i
k
a
b
d
f
h
i
l
a
b
d
f
h
j
k
a
b
d
f
h
j
l
a
b
d
f
h
k
l
a
b
d
f
i
j
k
a
b
d
f
i
j
l
a
b
d
f
i
k
l
a
b
d
f
j
k
l
a
b
d
g
h
i
j
a
b
d
g
h
i
k
a
b
d
g
h
i
l
a
b
d
g
h
j
k
a
b
d
g
h
j
l
a
b
d
g
h
k
l
a
b
d
g
i
j
k
a
b
d
g
i
j
l
a
b
d
g
i
k
l
a
b
d
g
j
k
l
a
b
d
h
i
j
k
a
b
d
h
i
j
l
a
b
d
h
i
k
l
a
b
d
h
j
k
l
a
b
d
i
j
k
l
a
b
e
f
g
h
i
a
b
e
f
g
h
j
a
b
e
f
g
h
k
a
b
e
f
g
h
l
a
b
e
f
g
i
j
a
b
e
f
g
i
k
a
b
e
f
g
i
l
a
b
e
f
g
j
k
a
b
e
f
g
j
l
a
b
e
f
g
k
l
a
b
e
f
h
i
j
a
b
e
f
h
i
k
a
b
e
f
h
i
l
a
b
e
f
h
j
k
a
b
e
f
h
j
l
a
b
e
f
h
k
l
a
b
e
f
i
j
k
a
b
e
f
i
j
l
a
b
e
f
i
k
l
a
b
e
f
j
k
l
a
b
e
g
h
i
j
a
b
e
g
h
i
k
a
b
e
g
h
i
l
a
b
e
g
h
j
k
a
b
e
g
h
j
l
a
b
e
g
h
k
l
a
b
e
g
i
j
k
a
b
e
g
i
j
l
a
b
e
g
i
k
l
a
b
e
g
j
k
l
a
b
e
h
i
j
k
a
b
e
h
i
j
l
a
b
e
h
i
k
l
a
b
e
h
j
k
l
a
b
e
i
j
k
l
a
b
f
g
h
i
j
a
b
f
g
h
i
k
a
b
f
g
h
i
l
a
b
f
g
h
j
k
a
b
f
g
h
j
l
a
b
f
g
h
k
l
a
b
f
g
i
j
k
a
b
f
g
i
j
l
a
b
f
g
i
k
l
a
b
f
g
j
k
l
a
b
f
h
i
j
k
a
b
f
h
i
j
l
a
b
f
h
i
k
l
a
b
f
h
j
k
l
a
b
f
i
j
k
l
a
b
g
h
i
j
k
a
b
g
h
i
j
l
a
b
g
h
i
k
l
a
b
g
h
j
k
l
a
b
g
i
j
k
l
a
b
h
i
j
k
l
a
c
d
e
f
g
h
a
c
d
e
f
g
i
a
c
d
e
f
g
j
a
c
d
e
f
g
k
a
c
d
e
f
g
l
a
c
d
e
f
h
i
a
c
d
e
f
h
j
a
c
d
e
f
h
k
a
c
d
e
f
h
l
a
c
d
e
f
i
j
a
c
d
e
f
i
k
a
c
d
e
f
i
l
a
c
d
e
f
j
k
a
c
d
e
f
j
l
a
c
d
e
f
k
l
a
c
d
e
g
h
i
a
c
d
e
g
h
j
a
c
d
e
g
h
k
a
c
d
e
g
h
l
a
c
d
e
g
i
j
a
c
d
e
g
i
k
a
c
d
e
g
i
l
a
c
d
e
g
j
k
a
c
d
e
g
j
l
a
c
d
e
g
k
l
a
c
d
e
h
i
j
a
c
d
e
h
i
k
a
c
d
e
h
i
l
a
c
d
e
h
j
k
a
c
d
e
h
j
l
a
c
d
e
h
k
l
a
c
d
e
i
j
k
a
c
d
e
i
j
l
a
c
d
e
i
k
l
a
c
d
e
j
k
l
a
c
d
f
g
h
i
a
c
d
f
g
h
j
a
c
d
f
g
h
k
a
c
d
f
g
h
l
a
c
d
f
g
i
j
a
c
d
f
g
i
k
a
c
d
f
g
i
l
a
c
d
f
g
j
k
a
c
d
f
g
j
l
a
c
d
f
g
k
l
a
c
d
f
h
i
j
a
c
d
f
h
i
k
a
c
d
f
h
i
l
a
c
d
f
h
j
k
a
c
d
f
h
j
l
a
c
d
f
h
k
l
a
c
d
f
i
j
k
a
c
d
f
i
j
l
a
c
d
f
i
k
l
a
c
d
f
j
k
l
a
c
d
g
h
i
j
a
c
d
g
h
i
k
a
c
d
g
h
i
l
a
c
d
g
h
j
k
a
c
d
g
h
j
l
a
c
d
g
h
k
l
a
c
d
g
i
j
k
a
c
d
g
i
j
l
a
c
d
g
i
k
l
a
c
d
g
j
k
l
a
c
d
h
i
j
k
a
c
d
h
i
j
l
a
c
d
h
i
k
l
a
c
d
h
j
k
l
a
c
d
i
j
k
l
a
c
e
f
g
h
i
a
c
e
f
g
h
j
a
c
e
f
g
h
k
a
c
e
f
g
h
l
a
c
e
f
g
i
j
a
c
e
f
g
i
k
a
c
e
f
g
i
l
a
c
e
f
g
j
k
a
c
e
f
g
j
l
a
c
e
f
g
k
l
a
c
e
f
h
i
j
a
c
e
f
h
i
k
a
c
e
f
h
i
l
a
c
e
f
h
j
k
a
c
e
f
h
j
l
a
c
e
f
h
k
l
a
c
e
f
i
j
k
a
c
e
f
i
j
l
a
c
e
f
i
k
l
a
c
e
f
j
k
l
a
c
e
g
h
i
j
a
c
e
g
h
i
k
a
c
e
g
h
i
l
a
c
e
g
h
j
k
a
c
e
g
h
j
l
a
c
e
g
h
k
l
a
c
e
g
i
j
k
a
c
e
g
i
j
l
a
c
e
g
i
k
l
a
c
e
g
j
k
l
a
c
e
h
i
j
k
a
c
e
h
i
j
l
a
c
e
h
i
k
l
a
c
e
h
j
k
l
a
c
e
i
j
k
l
a
c
f
g
h
i
j
a
c
f
g
h
i
k
a
c
f
g
h
i
l
a
c
f
g
h
j
k
a
c
f
g
h
j
l
a
c
f
g
h
k
l
a
c
f
g
i
j
k
a
c
f
g
i
j
l
a
c
f
g
i
k
l
a
c
f
g
j
k
l
a
c
f
h
i
j
k
a
c
f
h
i
j
l
a
c
f
h
i
k
l
a
c
f
h
j
k
l
a
c
f
i
j
k
l
a
c
g
h
i
j
k
a
c
g
h
i
j
l
a
c
g
h
i
k
l
a
c
g
h
j
k
l
a
c
g
i
j
k
l
a
c
h
i
j
k
l
a
d
e
f
g
h
i
a
d
e
f
g
h
j
a
d
e
f
g
h
k
a
d
e
f
g
h
l
a
d
e
f
g
i
j
a
d
e
f
g
i
k
a
d
e
f
g
i
l
a
d
e
f
g
j
k
a
d
e
f
g
j
l
a
d
e
f
g
k
l
a
d
e
f
h
i
j
a
d
e
f
h
i
k
a
d
e
f
h
i
l
a
d
e
f
h
j
k
a
d
e
f
h
j
l
a
d
e
f
h
k
l
a
d
e
f
i
j
k
a
d
e
f
i
j
l
a
d
e
f
i
k
l
a
d
e
f
j
k
l
a
d
e
g
h
i
j
a
d
e
g
h
i
k
a
d
e
g
h
i
l
a
d
e
g
h
j
k
a
d
e
g
h
j
l
a
d
e
g
h
k
l
a
d
e
g
i
j
k
a
d
e
g
i
j
l
a
d
e
g
i
k
l
a
d
e
g
j
k
l
a
d
e
h
i
j
k
a
d
e
h
i
j
l
a
d
e
h
i
k
l
a
d
e
h
j
k
l
a
d
e
i
j
k
l
a
d
f
g
h
i
j
a
d
f
g
h
i
k
a
d
f
g
h
i
l
a
d
f
g
h
j
k
a
d
f
g
h
j
l
a
d
f
g
h
k
l
a
d
f
g
i
j
k
a
d
f
g
i
j
l
a
d
f
g
i
k
l
a
d
f
g
j
k
l
a
d
f
h
i
j
k
a
d
f
h
i
j
l
a
d
f
h
i
k
l
a
d
f
h
j
k
l
a
d
f
i
j
k
l
a
d
g
h
i
j
k
a
d
g
h
i
j
l
a
d
g
h
i
k
l
a
d
g
h
j
k
l
a
d
g
i
j
k
l
a
d
h
i
j
k
l
a
e
f
g
h
i
j
a
e
f
g
h
i
k
a
e
f
g
h
i
l
a
e
f
g
h
j
k
a
e
f
g
h
j
l
a
e
f
g
h
k
l
a
e
f
g
i
j
k
a
e
f
g
i
j
l
a
e
f
g
i
k
l
a
e
f
g
j
k
l
a
e
f
h
i
j
k
a
e
f
h
i
j
l
a
e
f
h
i
k
l
a
e
f
h
j
k
l
a
e
f
i
j
k
l
a
e
g
h
i
j
k
a
e
g
h
i
j
l
a
e
g
h
i
k
l
a
e
g
h
j
k
l
a
e
g
i
j
k
l
a
e
h
i
j
k
l
a
f
g
h
i
j
k
a
f
g
h
i
j
l
a
f
g
h
i
k
l
a
f
g
h
j
k
l
a
f
g
i
j
k
l
a
f
h
i
j
k
l
a
g
h
i
j
k
l
b
c
d
e
f
g
h
b
c
d
e
f
g
i
b
c
d
e
f
g
j
b
c
d
e
f
g
k
b
c
d
e
f
g
l
b
c
d
e
f
h
i
b
c
d
e
f
h
j
b
c
d
e
f
h
k
b
c
d
e
f
h
l
b
c
d
e
f
i
j
b
c
d
e
f
i
k
b
c
d
e
f
i
l
b
c
d
e
f
j
k
b
c
d
e
f
j
l
b
c
d
e
f
k
l
b
c
d
e
g
h
i
b
c
d
e
g
h
j
b
c
d
e
g
h
k
b
c
d
e
g
h
l
b
c
d
e
g
i
j
b
c
d
e
g
i
k
b
c
d
e
g
i
l
b
c
d
e
g
j
k
b
c
d
e
g
j
l
b
c
d
e
g
k
l
b
c
d
e
h
i
j
b
c
d
e
h
i
k
b
c
d
e
h
i
l
b
c
d
e
h
j
k
b
c
d
e
h
j
l
b
c
d
e
h
k
l
b
c
d
e
i
j
k
b
c
d
e
i
j
l
b
c
d
e
i
k
l
b
c
d
e
j
k
l
b
c
d
f
g
h
i
b
c
d
f
g
h
j
b
c
d
f
g
h
k
b
c
d
f
g
h
l
b
c
d
f
g
i
j
b
c
d
f
g
i
k
b
c
d
f
g
i
l
b
c
d
f
g
j
k
b
c
d
f
g
j
l
b
c
d
f
g
k
l
b
c
d
f
h
i
j
b
c
d
f
h
i
k
b
c
d
f
h
i
l
b
c
d
f
h
j
k
b
c
d
f
h
j
l
b
c
d
f
h
k
l
b
c
d
f
i
j
k
b
c
d
f
i
j
l
b
c
d
f
i
k
l
b
c
d
f
j
k
l
b
c
d
g
h
i
j
b
c
d
g
h
i
k
b
c
d
g
h
i
l
b
c
d
g
h
j
k
b
c
d
g
h
j
l
b
c
d
g
h
k
l
b
c
d
g
i
j
k
b
c
d
g
i
j
l
b
c
d
g
i
k
l
b
c
d
g
j
k
l
b
c
d
h
i
j
k
b
c
d
h
i
j
l
b
c
d
h
i
k
l
b
c
d
h
j
k
l
b
c
d
i
j
k
l
b
c
e
f
g
h
i
b
c
e
f
g
h
j
b
c
e
f
g
h
k
b
c
e
f
g
h
l
b
c
e
f
g
i
j
b
c
e
f
g
i
k
b
c
e
f
g
i
l
b
c
e
f
g
j
k
b
c
e
f
g
j
l
b
c
e
f
g
k
l
b
c
e
f
h
i
j
b
c
e
f
h
i
k
b
c
e
f
h
i
l
b
c
e
f
h
j
k
b
c
e
f
h
j
l
b
c
e
f
h
k
l
b
c
e
f
i
j
k
b
c
e
f
i
j
l
b
c
e
f
i
k
l
b
c
e
f
j
k
l
b
c
e
g
h
i
j
b
c
e
g
h
i
k
b
c
e
g
h
i
l
b
c
e
g
h
j
k
b
c
e
g
h
j
l
b
c
e
g
h
k
l
b
c
e
g
i
j
k
b
c
e
g
i
j
l
b
c
e
g
i
k
l
b
c
e
g
j
k
l
b
c
e
h
i
j
k
b
c
e
h
i
j
l
b
c
e
h
i
k
l
b
c
e
h
j
k
l
b
c
e
i
j
k
l
b
c
f
g
h
i
j
b
c
f
g
h
i
k
b
c
f
g
h
i
l
b
c
f
g
h
j
k
b
c
f
g
h
j
l
b
c
f
g
h
k
l
b
c
f
g
i
j
k
b
c
f
g
i
j
l
b
c
f
g
i
k
l
b
c
f
g
j
k
l
b
c
f
h
i
j
k
b
c
f
h
i
j
l
b
c
f
h
i
k
l
b
c
f
h
j
k
l
b
c
f
i
j
k
l
b
c
g
h
i
j
k
b
c
g
h
i
j
l
b
c
g
h
i
k
l
b
c
g
h
j
k
l
b
c
g
i
j
k
l
b
c
h
i
j
k
l
b
d
e
f
g
h
i
b
d
e
f
g
h
j
b
d
e
f
g
h
k
b
d
e
f
g
h
l
b
d
e
f
g
i
j
b
d
e
f
g
i
k
b
d
e
f
g
i
l
b
d
e
f
g
j
k
b
d
e
f
g
j
l
b
d
e
f
g
k
l
b
d
e
f
h
i
j
b
d
e
f
h
i
k
b
d
e
f
h
i
l
b
d
e
f
h
j
k
b
d
e
f
h
j
l
b
d
e
f
h
k
l
b
d
e
f
i
j
k
b
d
e
f
i
j
l
b
d
e
f
i
k
l
b
d
e
f
j
k
l
b
d
e
g
h
i
j
b
d
e
g
h
i
k
b
d
e
g
h
i
l
b
d
e
g
h
j
k
b
d
e
g
h
j
l
b
d
e
g
h
k
l
b
d
e
g
i
j
k
b
d
e
g
i
j
l
b
d
e
g
i
k
l
b
d
e
g
j
k
l
b
d
e
h
i
j
k
b
d
e
h
i
j
l
b
d
e
h
i
k
l
b
d
e
h
j
k
l
b
d
e
i
j
k
l
b
d
f
g
h
i
j
b
d
f
g
h
i
k
b
d
f
g
h
i
l
b
d
f
g
h
j
k
b
d
f
g
h
j
l
b
d
f
g
h
k
l
b
d
f
g
i
j
k
b
d
f
g
i
j
l
b
d
f
g
i
k
l
b
d
f
g
j
k
l
b
d
f
h
i
j
k
b
d
f
h
i
j
l
b
d
f
h
i
k
l
b
d
f
h
j
k
l
b
d
f
i
j
k
l
b
d
g
h
i
j
k
b
d
g
h
i
j
l
b
d
g
h
i
k
l
b
d
g
h
j
k
l
b
d
g
i
j
k
l
b
d
h
i
j
k
l
b
e
f
g
h
i
j
b
e
f
g
h
i
k
b
e
f
g
h
i
l
b
e
f
g
h
j
k
b
e
f
g
h
j
l
b
e
f
g
h
k
l
b
e
f
g
i
j
k
b
e
f
g
i
j
l
b
e
f
g
i
k
l
b
e
f
g
j
k
l
b
e
f
h
i
j
k
b
e
f
h
i
j
l
b
e
f
h
i
k
l
b
e
f
h
j
k
l
b
e
f
i
j
k
l
b
e
g
h
i
j
k
b
e
g
h
i
j
l
b
e
g
h
i
k
l
b
e
g
h
j
k
l
b
e
g
i
j
k
l
b
e
h
i
j
k
l
b
f
g
h
i
j
k
b
f
g
h
i
j
l
b
f
g
h
i
k
l
b
f
g
h
j
k
l
b
f
g
i
j
k
l
b
f
h
i
j
k
l
b
g
h
i
j
k
l
c
d
e
f
g
h
i
c
d
e
f
g
h
j
c
d
e
f
g
h
k
c
d
e
f
g
h
l
c
d
e
f
g
i
j
c
d
e
f
g
i
k
c
d
e
f
g
i
l
c
d
e
f
g
j
k
c
d
e
f
g
j
l
c
d
e
f
g
k
l
c
d
e
f
h
i
j
c
d
e
f
h
i
k
c
d
e
f
h
i
l
c
d
e
f
h
j
k
c
d
e
f
h
j
l
c
d
e
f
h
k
l
c
d
e
f
i
j
k
c
d
e
f
i
j
l
c
d
e
f
i
k
l
c
d
e
f
j
k
l
c
d
e
g
h
i
j
c
d
e
g
h
i
k
c
d
e
g
h
i
l
c
d
e
g
h
j
k
c
d
e
g
h
j
l
c
d
e
g
h
k
l
c
d
e
g
i
j
k
c
d
e
g
i
j
l
c
d
e
g
i
k
l
c
d
e
g
j
k
l
c
d
e
h
i
j
k
c
d
e
h
i
j
l
c
d
e
h
i
k
l
c
d
e
h
j
k
l
c
d
e
i
j
k
l
c
d
f
g
h
i
j
c
d
f
g
h
i
k
c
d
f
g
h
i
l
c
d
f
g
h
j
k
c
d
f
g
h
j
l
c
d
f
g
h
k
l
c
d
f
g
i
j
k
c
d
f
g
i
j
l
c
d
f
g
i
k
l
c
d
f
g
j
k
l
c
d
f
h
i
j
k
c
d
f
h
i
j
l
c
d
f
h
i
k
l
c
d
f
h
j
k
l
c
d
f
i
j
k
l
c
d
g
h
i
j
k
c
d
g
h
i
j
l
c
d
g
h
i
k
l
c
d
g
h
j
k
l
c
d
g
i
j
k
l
c
d
h
i
j
k
l
c
e
f
g
h
i
j
c
e
f
g
h
i
k
c
e
f
g
h
i
l
c
e
f
g
h
j
k
c
e
f
g
h
j
l
c
e
f
g
h
k
l
c
e
f
g
i
j
k
c
e
f
g
i
j
l
c
e
f
g
i
k
l
c
e
f
g
j
k
l
c
e
f
h
i
j
k
c
e
f
h
i
j
l
c
e
f
h
i
k
l
c
e
f
h
j
k
l
c
e
f
i
j
k
l
c
e
g
h
i
j
k
c
e
g
h
i
j
l
c
e
g
h
i
k
l
c
e
g
h
j
k
l
c
e
g
i
j
k
l
c
e
h
i
j
k
l
c
f
g
h
i
j
k
c
f
g
h
i
j
l
c
f
g
h
i
k
l
c
f
g
h
j
k
l
c
f
g
i
j
k
l
c
f
h
i
j
k
l
c
g
h
i
j
k
l
d
e
f
g
h
i
j
d
e
f
g
h
i
k
d
e
f
g
h
i
l
d
e
f
g
h
j
k
d
e
f
g
h
j
l
d
e
f
g
h
k
l
d
e
f
g
i
j
k
d
e
f
g
i
j
l
d
e
f
g
i
k
l
d
e
f
g
j
k
l
d
e
f
h
i
j
k
d
e
f
h
i
j
l
d
e
f
h
i
k
l
d
e
f
h
j
k
l
d
e
f
i
j
k
l
d
e
g
h
i
j
k
d
e
g
h
i
j
l
d
e
g
h
i
k
l
d
e
g
h
j
k
l
d
e
g
i
j
k
l
d
e
h
i
j
k
l
d
f
g
h
i
j
k
d
f
g
h
i
j
l
d
f
g
h
i
k
l
d
f
g
h
j
k
l
d
f
g
i
j
k
l
d
f
h
i
j
k
l
d
g
h
i
j
k
l
e
f
g
h
i
j
k
e
f
g
h
i
j
l
e
f
g
h
i
k
l
e
f
g
h
j
k
l
e
f
g
i
j
k
l
e
f
h
i
j
k
l
e
g
h
i
j
k
l
f
g
h
i
j
k
l
"
*/
#include <stdio.h>
int a[26]; 
void array(int a[],int k)
{
    int i;
    for(i=0;i<k;i++)
    {
        printf("%c\n",a[i]+96);
    }
}
void wellOrderdStrings(int a[],int n,int k,int i)
{
    int j;
    if(i==k)
    {
        array(a,k);
    }
    else if(i<k)
    {
        for(j=(i>0)?a[i-1]+1:1;j<=n;j++)
        {
            a[i]=j;
            wellOrderdStrings(a,n,k,i+1);    
        }
    }
}
int main()
{
    int n,k,i=0;
    scanf("%d%d",&n,&k);
    wellOrderdStrings(a,n,k,i);
    return 0;
}
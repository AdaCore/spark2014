This example contains multiple variants of substring search:

* a simple brute force search in `Brute_Force` and `Brute_Force_Slice`.
* a more efficient algorithm called quick search in `QS`.

The postcondition of all variants expresses that the search is successful
if-and-only-if the string `Haystack` contains the substring `Needle`
searched, and if so the index returned is one at which the string contains this
substring. GNATprove proves all checks on these programs. A detailed account
of the development and verification of this example is given in the
[corresponding post on the AdaCore
blog](https://blog.adacore.com/applied-formal-logic-searching-in-strings).

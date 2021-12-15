This program implements a toy interface to a bank account database, with
procedures to deposit and withdraw money, and functions to query the account
balance and information. This program was used as running example in the article
[Integrating Formal Program Verification with
Testing](http://www.adacore.com/uploads_gems/Hi-Lite_ERTS-2012.pdf). The API is
annotated with full functional contracts, as well as test cases expressed with
aspect `Test_Case`. GNATprove proves all checks on this program.

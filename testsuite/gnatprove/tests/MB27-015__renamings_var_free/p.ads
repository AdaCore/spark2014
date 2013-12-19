-- MB27-015 - legality of variables in expressions.
--
-- This test case shows examples of both legal and illegal
-- use of variables inside indexing expressions and slices
--
-- See SPARK LRM 4.4(2) fifth bullet.
package P
is
    X : Integer := 2;
    Y : String  := "123";

    Named_Constant : constant Integer := X;

    Illegal_Index_Rename : Character renames Y (X);

    Legal_Index_Rename   : Character renames Y (Named_Constant);

    Illegal_Slice_Rename : String renames Y (1 .. X);

    Legal_Slice_Rename   : String renames Y (1 .. Named_Constant);

end P;


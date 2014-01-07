-- MB27-015 - legality of variables in expressions.
--
-- This test case shows examples of both legal and illegal
-- use of variables inside indexing expressions, slices,
-- and inside the parameters of attribute references.
--
-- See SPARK LRM 4.4(2) fifth bullet.
package P
is
    X : Integer := 2;
    Y : String  := "123";
    Z : Integer := 3;
    C : constant Integer := 3;

    Named_Constant : constant Integer := X;

    -- renaming of an indexed_component of an array object
    Illegal_Index_Rename : Character renames Y (X); -- illegal
    Legal_Index_Rename   : Character renames Y (Named_Constant); -- legal

    -- renaming of a slice of an array object
    Illegal_Slice_Rename : String renames Y (1 .. X); -- illegal
    Legal_Slice_Rename   : String renames Y (1 .. Named_Constant); -- legal


    -- Renamings involving attribute_reference

    -- Attribute with 1 param, literal
    AR2 : Integer renames Integer'Succ (1); -- legal

    -- Attribute with 1 param, variable
    AR3 : Integer renames Integer'Succ (X); -- legal

    -- Attribute with 2 params, literals and constants
    AR4 : Integer renames Integer'Max (1, 2); -- legal
    AR5 : Integer renames Integer'Max (1, C); -- legal
    AR6 : Integer renames Integer'Max (C, 1); -- legal

    -- Attribute with 2 params, literals and variables
    AR7 : Integer renames Integer'Max (X, 1); -- legal
    AR8 : Integer renames Integer'Max (1, X); -- legal
    AR9 : Integer renames Integer'Max (X, Z); -- legal

end P;

package Update is

   type Index is range 1 .. 8;

   type Array_3D is array (Index, Index, Index) of Integer;

   X : Integer;
   An_Arr : Array_3D := Array_3D'(others => (others => (others => 7)));

   ----------------------------------------------------------------------------
   -- 'Update Array tests
   ----------------------------------------------------------------------------

   --  basic array update, loop reference test
   procedure Basic_Array_Update (A: in out Array_3D;
                                 I: in Index;
                                 New_Val: in Integer)
     with Post => (for all J in Index =>
                     (for all K in Index =>
                        (for all L in Index =>
                           (if I /= J or I /= K or I /= L then
                             A(J, K, L) = A'Old(J, J, J)
                           else A(J, K, L) = New_Val))));

   --  same basic array test using 'Update, one dynamic choice,
   --  prefix is in/out parameter
   procedure Basic_Array_Update2 (A: in out Array_3D;
                                  I: in Index;
                                  New_Val: in Integer)
     with Post => A = A'Old'Update((I, I, I) => New_Val);

end Update;

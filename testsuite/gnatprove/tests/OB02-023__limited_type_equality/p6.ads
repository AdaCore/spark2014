with P3;

package P6 is

   type Index is new Integer range 1 .. 3;

   type Array_of_Limited_Records_With_User_Eq is array (Index) of P3.Limited_Record_With_User_Eq;

   function "=" (Left, Right : Array_of_Limited_Records_With_User_Eq) return Boolean is
     (for all X in Index => P3."=" (Left (X), Right (X)));

end;

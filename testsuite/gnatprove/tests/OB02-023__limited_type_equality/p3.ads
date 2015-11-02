package p3 is

   type Limited_Record_With_User_Eq is limited
      record
         X : Integer;
      end record;

   function "=" (Left, Right : Limited_Record_With_User_Eq) return Boolean is
     (Left.X = Right.X);

end;

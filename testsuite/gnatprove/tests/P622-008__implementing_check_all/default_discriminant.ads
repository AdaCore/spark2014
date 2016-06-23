package Default_Discriminant is

   X : Integer := 0;
   Y : Integer;

   type Empty_Record (D : Integer := X) is
      record
         null;
      end record;

    procedure P;

end Default_Discriminant;

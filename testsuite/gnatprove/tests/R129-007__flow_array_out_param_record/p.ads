package P is
   type My_Rec (Len : Integer) is record
      A : String (1 .. Len);
   end record;

   procedure Proc (S : out My_Rec) with
     Depends => (S => null);

end P;

package Discr_Rec is

   type Rec (Size : Natural := Standard'Word_Size) is
     record
        A : String (1 .. Size);
     end record;

   type Empty_Rec (Size : Natural := Standard'Word_Size) is
     record
        null;
     end record;
end;

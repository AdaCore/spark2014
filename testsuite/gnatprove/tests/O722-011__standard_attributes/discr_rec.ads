package Discr_Rec is

   type Rec (Size : Natural := Standard'Word_Size) is
     record
        A : String (1 .. Size);
     end record;
end;

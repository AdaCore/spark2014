with List_Allocator; use List_Allocator;

procedure Test_Allocator is
   Res1, Res2, Res3, Res4 : Resource;
begin
   Alloc (Res1);
   pragma Assert (Res1 /= No_Resource);
   pragma Assert (Is_Allocated (Res1));
   Alloc (Res2);
   pragma Assert (Res2 /= No_Resource);
   pragma Assert (Is_Allocated (Res2));
   Alloc (Res3);
   pragma Assert (Res3 /= No_Resource);
   pragma Assert (Is_Allocated (Res3));
   Alloc (Res4);
   pragma Assert (Res4 /= No_Resource);
   Free (Res1);
   pragma Assert (Is_Available (Res1));
   Free (Res2);
   pragma Assert (Is_Available (Res2));
   Free (Res3);
   pragma Assert (Is_Available (Res3));
end Test_Allocator;

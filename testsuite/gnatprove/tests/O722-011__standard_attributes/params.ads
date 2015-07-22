package Params is

   procedure Address_Size (X : Natural := Standard'Address_Size);
   procedure Maximum_Alignment (X : Natural := Standard'Maximum_Alignment);
   procedure Storage_Unit (X : Natural := Standard'Storage_Unit);
   procedure System_Allocator_Alignment (X : Natural := Standard'System_Allocator_Alignment);
   procedure Wchar_T_Size (X : Natural := Standard'Wchar_T_Size);
   procedure Word_Size (X : Natural := Standard'Word_Size);

end;

package Foo is

   type Ptr_T is access all Integer;

   subtype Ptr_T_Alias is Ptr_T;

   type New_Ptr_T is new Ptr_T_Alias;

end;

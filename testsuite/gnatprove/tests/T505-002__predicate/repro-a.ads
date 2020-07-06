package Repro.A
is

   subtype Opt_Index_Type is Natural range 0 .. 80;
   subtype Index_Type is Opt_Index_Type range 1 .. Opt_Index_Type'Last;

   type String_Type_Base is record
      Str  : String (Index_Type);
      Last : Integer;
   end record;

   subtype String_Type is String_Type_Base
   with Dynamic_Predicate => String_Type.Last in Index_Type;

   type Foo_Type_Base is record
      X : String_Type_Base;
      Y : String_Type_Base;
   end record;

   subtype Foo_Type is Foo_Type_Base
   with Dynamic_Predicate =>
     Foo_Type.X in String_Type and
     Foo_Type.Y in String_Type;

end Repro.A;

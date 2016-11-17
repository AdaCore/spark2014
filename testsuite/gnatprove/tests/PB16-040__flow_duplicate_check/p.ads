package P is

   subtype Str_Length is Natural range 0 .. 10;
   subtype Str_Index  is Str_Length range 1 .. Str_Length'Last;
   subtype Str_String is String (Str_Index);

   type Str is record
      Length : Str_Length;
      Value  : Str_String;
   end record;

   procedure Copy (Source : in     String;
                   Target :    out Str)
   with Global => null;

end P;

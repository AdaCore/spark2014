package body Usergroup_Examples
is
   type Rec_T is record
      A : Integer;
      B : Integer;
      C : Integer;
   end record;

   type Index_T is range 1 .. 100;
   type Array_Rec_T is array (Index_T) of Rec_T;

   type U64 is mod 2 ** 64;
   subtype Hash_Position is Integer range 1 .. 2 ** 8;
   type Hash_Table is array (Hash_Position) of Rec_T;

   type Value_T is new Integer;

   type Value_Array is array (Index_T) of Value_T;

   type Value_Cache_T is record
      Cached : Boolean;
      Cache  : Value_T;
   end record;

   type Value_Cache_Array is
     array (Index_T) of Value_Cache_T;

   function Is_Valid (V : Value_T) return Boolean
     with Ghost,
          Import,
          Global   => null;

   procedure Example_2 (AR      : in out Array_Rec_T;
                        Current : in out Index_T)
     with Depends => ((AR, Current) =>+ Current)
   is
   begin
      AR (Current).A := 0;
      Current := (Current + 1) mod Index_T'Last;  --  @RANGE_CHECK:FAIL
   end Example_2;


   function Example_3 (HT   : in Hash_Table;
                       Salt : in U64;
                       Hash : in U64)
                       return Integer
   is
      Tmp : U64;
   begin
      Tmp := (5 * Salt) xor (7 * Hash);

      return HT (Integer (Tmp) mod Hash_Position'Last).A;  --  @INDEX_CHECK:FAIL
   end Example_3;


   function Example_5 (A : in U64;
                       B : in U64)
                       return U64
     with Pre  => A > 17 and B > 19,
          Post => Example_5'Result > 0
   is
   begin
      return 73 xor (A * B);
   end Example_5;

   procedure Example_6 (VA  : in     Value_Array;
                        VCA : in out Value_Cache_Array;
                        I   : in     Index_T;
                        V   :    out Value_T)
     with Depends => ((V, VCA) => (I, VA, VCA)),
          Pre     => (for all X in Index_T => Is_Valid (VA (X)))
                        and (for all Y in Index_T =>
                               (if VCA(Y).Cached then VCA(Y).Cache = VA (Y))),
          Post    => Is_Valid (V)
   is
   begin
      if VCA (I).Cached then
         V := VCA (I).Cache;
      else
         VCA (I).Cache  := VA (I);
         VCA (I).Cached := True;
         V              := VCA (I).Cache;
      end if;
   end Example_6;

   procedure Example_6_Fixed (VA  : in     Value_Array;
                              VCA : in out Value_Cache_Array;
                              I   : in     Index_T;
                              V   :    out Value_T)
     with Depends => ((V, VCA) => (I, VA, VCA)),
          Pre     => (for all X in Index_T => Is_Valid (VA (X)))
                        and (for all Y in Index_T =>
                               (if VCA (Y).Cached then VCA(Y).Cache = VA (Y))),
          Post    => Is_Valid(V)

   is
   begin
      if VCA (I).Cached then
         V := VCA (I).Cache;
      else
         VCA (I).Cache  := VA (I);
         VCA (I).Cached := True;
         V              := VCA (I).Cache;
      end if;
      pragma Assert (Is_Valid (VA (I)));
   end Example_6_Fixed;

end Usergroup_Examples;

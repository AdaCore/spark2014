package body Test
is

   function XOR2 (V0, V1 : Word32) return Word32
   is
   begin
      return V0 xor V1;
   end XOR2;

   ----------------------------------------------------------------------------

   procedure Block_XOR
     (Left   : in     Word32_Array_Type;
      Right  : in     Word32_Array_Type;
      Result :    out Word32_Array_Type)
   is
   begin
      for I in Index range Result'First .. Result'Last
      loop
         Result (I) := XOR2 (Left (I), Right (I));
         pragma Loop_Invariant
           (for all Pos in Index range Result'First .. I =>
              (Result (Pos) = XOR2 (Left (Pos), Right (Pos))));
      end loop;
   end Block_XOR;

   procedure Block_XOR_2
     (Left   : in     Word32_Array_Type;
      Right  : in     Word32_Array_Type;
      Result :    out Word32_Array_Type)
   is
   begin
      for I in Index range Result'First .. Result'Last
      loop
         Result (I) := XOR2 (Left (I), Right (I));
         pragma Loop_Invariant
           (for all Pos in Index range Result'First .. I =>
              (Result (Pos) = XOR2 (Left (Pos), Right (Pos))));
      end loop;
   end Block_XOR_2;
   pragma Annotate
     (GNATprove, False_Positive,
      """Result"" might not be initialized",
      "Initialized in complete loop");
end Test;

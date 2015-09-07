pragma SPARK_Mode(On);
with Interfaces.C;
package body Messages_Wrapper is
   use type Interfaces.C.size_t;  -- needed for visibility in precondition

   function Compute_Fletcher_Checksum
           (Buffer : in Interfaces.C.char_array;
            Size   : in Interfaces.C.size_t) return Interfaces.C.unsigned_short
      with
         Global        => null,
         Import        => True,
         Convention    => C,
         Pre           => Size = Buffer'Length,
         External_Name => "compute_fletcher_checksum";

   function Compute_Checksum (Data : in String) return Checksum_Type is
      -- Copy the Ada string Data into the C string Buffer
      Buffer : Interfaces.C.char_array :=
                 Interfaces.C.To_C (Item       => Data,
                                    Append_Nul => False);
      Result : Interfaces.C.unsigned_short;
   begin
      -- Call the C function whose Ada specification is above
      Result := Compute_Fletcher_Checksum (Buffer => Buffer,
                                           Size   => Buffer'Length);
      -- Return the Result converted to Checksum_Type;
      return Checksum_Type (Result);
   end Compute_Checksum;
end Messages_Wrapper;

with Code_Config;
with Interfaces; use Interfaces;

package body Bits_Manipulation.Functions with SPARK_Mode is

   function Shift_Right (V : Modular; Amount : Natural) return Modular is
     (case Modular_Size is
         when 1 .. 8   => Modular (Shift_Right (Unsigned_8 (V), Amount)),
         when 9 .. 16  => Modular (Shift_Right (Unsigned_16 (V), Amount)),
         when 17 .. 32 => Modular (Shift_Right (Unsigned_32 (V), Amount)),
         when others   => Modular (Shift_Right (Unsigned_64 (V), Amount)));

   function Shift_Left (V : Modular; Amount : Natural) return Modular is
     (case Modular_Size is
         when 1 .. 8   => Modular'Mod (Shift_Left (Unsigned_8 (V), Amount)),
         when 9 .. 16  => Modular'Mod (Shift_Left (Unsigned_16 (V), Amount)),
         when 17 .. 32 => Modular'Mod (Shift_Left (Unsigned_32 (V), Amount)),
         when others   => Modular'Mod (Shift_Left (Unsigned_64 (V), Amount)));

   function Make_Mask (Num_Bits : Mask_Size) return Modular is
     (Shift_Right (Modular'Last, Modular_Size - Num_Bits));

   function Extract_Bits_Inline_Always (Value : Modular; From, To : Bit_Position)
                                 return Modular
     with Inline_Always,
       Pre    => (To >= From),
       Post   => ((Extract_Bits_Inline_Always'Result =
                  (Shift_Right (Value, From) and Make_Mask (Mask_Size (To - From + 1))))
                  and then (Extract_Bits_Inline_Always'Result <= Make_Mask (Mask_Size (To - From + 1)))
                  and then (Shift_Left (Extract_Bits_Inline_Always'Result, From) =
                    (Value and Shift_Left(Make_Mask (Mask_Size (To - From + 1)), From))))
   is
      Len    : constant Natural := To - From + 1;
      Mask   : constant Modular := Make_Mask (Len);
      Result : Modular;
   begin
      Result := Shift_Right (Value,  From) and Mask;
      pragma Assert (Result <= Mask);
      return Result;
   end Extract_Bits_Inline_Always;

   function Extract_Bits_Inline (Value : Modular; From, To : Bit_Position)
                                 return Modular
   is (Extract_Bits_Inline_Always (Value, From, To))
   with Inline,
     Pre    => (To >= From),
     Post   => ((Extract_Bits_Inline'Result =
                (Shift_Right (Value, From) and Make_Mask (Mask_Size (To - From + 1))))
                and then (Extract_Bits_Inline'Result <= Make_Mask (Mask_Size (To - From + 1)))
                and then (Shift_Left (Extract_Bits_Inline'Result, From) =
                  (Value and Shift_Left (Make_Mask (Mask_Size (To - From + 1)), From))));

   function Extract_Bits_Not_Inline (Value : Modular; From, To : Bit_Position)
                                     return Modular
   is (Extract_Bits_Inline_Always (Value, From, To))
   with
     Pre    => (To >= From),
     Post   => ((Extract_Bits_Not_Inline'Result =
                (Shift_Right (Value, From) and Make_Mask (Mask_Size (To - From + 1))))
                and then (Extract_Bits_Not_Inline'Result <= Make_Mask (Mask_Size (To - From + 1)))
                and then (Shift_Left (Extract_Bits_Not_Inline'Result, From) =
                  (Value and Shift_Left (Make_Mask (Mask_Size (To - From + 1)), From))));

   function Extract_Bits (Value : Modular; From, To : Bit_Position)
                          return Modular is
   begin
      return Result : Modular do
         case Code_Parameters.Inline is
            when Code_Config.Default       =>
               Result := Extract_Bits_Not_Inline (Value, From, To);
            when Code_Config.Inline        =>
               Result := Extract_Bits_Inline (Value, From, To);
            when Code_Config.Inline_Always =>
               Result := Extract_Bits_Inline_Always (Value, From, To);
         end case;
      end return;
   end;

   function MSB_Index_Fast_Inline_Always (Value : Modular) return Bit_Position
     with Inline_Always,
     Pre => Value /= 0,
     Post => Shift_Right (Value , MSB_Index_Fast_Inline_Always'Result) = 1
   is
      Shift_Amount : Bit_Position := Bit_Position'Last / 2;
      Result       : Bit_Position := 0;
      V            : Modular := Value;
      New_V        : Modular;
   begin
      while Shift_Amount /= 0 and V /= 0 loop
         New_V := Shift_Right (V, Shift_Amount);
         if New_V /= 0 then
            pragma Assume (Result + Shift_Amount in Bit_Position);
            Result := Result + Shift_Amount;
            V := New_V;
         end if;
         Shift_Amount := (if Shift_Amount = 1
                          then 1
                          else Shift_Amount / 2);
      end loop;
      return Result;
   end MSB_Index_Fast_Inline_Always;

   function MSB_Index_Fast_Inline (Value : Modular) return Bit_Position
   is (MSB_Index_Fast_Inline_Always (Value))
   with Inline,
   Pre => Value /= 0,
   Post => Shift_Right (Value , MSB_Index_Fast_Inline'Result) = 1;

   function MSB_Index_Fast_Not_Inline (Value : Modular) return Bit_Position
   is (MSB_Index_Fast_Inline_Always (Value))
   with
   Pre => Value /= 0,
   Post => Shift_Right (Value , MSB_Index_Fast_Not_Inline'Result) = 1;

   function MSB_Index_Slow_Inline_Always (Value : Modular) return Bit_Position
     with Inline_Always,
     Pre => Value /= 0,
     Post => Shift_Right (Value , MSB_Index_Slow_Inline_Always'Result) = 1
   is
      Result : Bit_Position;
   begin
      pragma Assume (Lemmas.Shift_Right.Lemma6);
      for i in Bit_Position loop
         Result := i;
         exit when Shift_Right (Value, i) = 1;
         pragma Loop_Invariant (for all j in 0 .. i => Shift_Right (Value, j) > 1);
      end loop;
      return Result;
   end MSB_Index_Slow_Inline_Always;

   function MSB_Index_Slow_Inline (Value : Modular) return Bit_Position
   is (MSB_Index_Slow_Inline_Always (Value))
   with Inline,
   Pre => Value /= 0,
   Post => Shift_Right (Value , MSB_Index_Slow_Inline'Result) = 1;

   function MSB_Index_Slow_Not_Inline (Value : Modular) return Bit_Position
   is (MSB_Index_Slow_Inline_Always (Value))
   with
   Pre => Value /= 0,
   Post => Shift_Right (Value , MSB_Index_Slow_Not_Inline'Result) = 1;


   function MSB_Index (Value : Modular) return Bit_Position is
   begin
      return Result : Bit_Position do
         case Code_Parameters.Optimize_For is
            when Code_Config.Slow_And_Small =>
               case Code_Parameters.Inline is
                  when Code_Config.Inline_Always =>
                     Result := MSB_Index_Slow_Inline_Always (Value);
                  when Code_Config.Inline =>
                     Result := MSB_Index_Slow_Inline (Value);
                  when Code_Config.Default =>
                     Result := MSB_Index_Slow_Not_Inline (Value);
               end case;
            when others                     =>
               case Code_Parameters.Inline is
                  when Code_Config.Inline_Always =>
                     Result := MSB_Index_Fast_Inline_Always (Value);
                  when Code_Config.Inline =>
                     Result := MSB_Index_Fast_Inline (Value);
                  when Code_Config.Default =>
                     Result := MSB_Index_Fast_Not_Inline (Value);
               end case;
         end case;
      end return;
   end MSB_Index;

   package body Proofs is
      package body Make_Mask is

         function Lemma1 return Boolean is
            function Lemma1_Goal return Boolean
              with Import,
              Pre => (Lemmas.Make_Mask.Assertions.Lemma1);

         begin
            pragma Assume (Lemmas.Shift_Right.Lemma8);
            pragma Assert (for all Size in Mask_Size'First .. Mask_Size'Last - 1 =>
                             Functions.Make_Mask (Size) < Modular (2) ** (Size));
            return Lemma1_Goal;
         end Lemma1;

         function Lemma2 return Boolean is
            function Lemma2_Goal return Boolean
              with Import,
              Pre => (Lemmas.Make_Mask.Assertions.Lemma2);

            function Axiom return Boolean
              with Import,
              Post => (if Axiom'Result then
                         (for all V in Modular =>
                              (for all N in Bit_Position =>
                                   (if (V and 2 ** N) = 0 then
                                      ((V + 2 ** N) and 2 ** N) = 2 ** N))));

            function Ones (Amount : Mask_Size) return Modular
              with Post => (for all i in Mask_Size'First .. Amount =>
                              (Ones'Result and 2 ** (i - 1)) = 2 ** (i - 1))
            is
               Result : Modular := 0;
            begin
               pragma Assume (Axiom);
               for i in Mask_Size'First .. Amount loop
                  Result := Result + 2 ** (i - 1);
                  pragma Loop_Invariant ((Result and 2 ** (i - 1)) = 2 ** (i - 1));
               end loop;
               return Result;
            end Ones;

         begin
            pragma Assume (Lemmas.Shift_Right.Lemma8);
            pragma Assert (Functions.Make_Mask (1) = Modular (2) ** 1 - 1);
            for i in Mask_Size'First + 1 .. Mask_Size'Last - 1 loop
               pragma Assert (Functions.Make_Mask (i) = Modular (2) ** i - 1);
               pragma Loop_Invariant (for all j in Mask_Size'First .. i - 1 =>
                                         Functions.Make_Mask (j) = Modular (2) ** j - 1);
            end loop;
            pragma Assert (for all Size in Mask_Size'First .. Mask_Size'Last - 1 =>
                             Functions.Make_Mask (Size) = Modular (2) ** (Size) - 1);
            return Lemma2_Goal;
         end Lemma2;

      end Make_Mask;
   end Proofs;

end Bits_Manipulation.Functions;

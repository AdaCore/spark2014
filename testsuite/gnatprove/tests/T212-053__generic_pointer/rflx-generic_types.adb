with RFLX.Lemmas;

package body RFLX.Generic_Types with
  SPARK_Mode
is

   function Extract (Data   : Array_Type;
                     Offset : Offset_Type) return Value_Type
   is
      pragma Assert (Element_Type'Pos (Element_Type'First) = 0);
      pragma Assert (Element_Type'Pos (Element_Type'Last) = 2**Element_Type'Size - 1);

      LSB_Offset : constant Long_Integer := Offset_Type'Pos (Offset);

      --  Index pointing to least significant element
      Least_Significant_Index : constant Long_Integer := LSB_Offset / Element_Type'Size;

      --  Bits the least significant element (LSE) is shifted left relative to a single element
      LSE_Offset : constant Natural := Natural (LSB_Offset mod Element_Type'Size);

      --  Index pointing to most significant index
      Most_Significant_Index : constant Long_Integer :=
        (LSB_Offset + Long_Integer (Value_Type'Size) - 1) / Element_Type'Size;

      --  Bits the most significant element (MSE) is shifted right relative to a single element
      MSE_Offset : constant Natural := Element_Type'Size - LSE_Offset;

      function D (Index : Long_Integer) return Element_Type with
        Pre => Index >= 0 and then Index < Data'Length;

      function D (Index : Long_Integer) return Element_Type
      is
         function ES return Natural is (Element_Type'Size) with Post => ES'Result = Element_Type'Size;
         E : constant Natural := (LSE_Offset + Value_Type'Size + Element_Type'Size - 1) mod ES + 1;
         pragma Assert (2**Element_Type'Size = 2**ES);
      begin
         declare
            Mask : constant Long_Integer := (if Index < Most_Significant_Index then 2**ES else 2**E);
            Val  : constant Element_Type := Data (Index_Type'Val ((Index_Type'Pos (Data'Last) - Index)));
         begin
            return Element_Type'Val (Element_Type'Pos (Val) mod Mask);
         end;
      end D;

      type Result_Type is mod 2**Long_Integer'Size;
      Result : Result_Type := 0;

      function LIS return Natural is (Long_Integer'Size) with Post => LIS'Result = Long_Integer'Size;
      pragma Assert (2**(LIS - 2) - 1 = 2**(Long_Integer'Size - 2) - 1);
      --  WORKAROUND: Componolit/Workarounds#15
      pragma Annotate (GNATprove, False_Positive, "assertion",
                       "solvers cannot show correspondence between integers and exponentiation abstraction");
      pragma Annotate (GNATprove, False_Positive, "overflow",
                       "solvers cannot show that overflow does not occur for 2**62");
      Pow2_LSE_Offset : constant Long_Integer := 2**LSE_Offset;

   begin
      pragma Assert (Value_Type'Size - Value_Type'Size mod Element_Type'Size
                     = Element_Type'Size * (Value_Type'Size / Element_Type'Size));

      for I in Least_Significant_Index .. Most_Significant_Index - 1
      loop
         declare
            D_Current : constant Element_Type := D (I);
            D_Next    : constant Element_Type := D (I + 1);
         begin
            Lemmas.Mult_Limit (Element_Type'Pos (D_Next) mod Pow2_LSE_Offset, LSE_Offset, 2**MSE_Offset, MSE_Offset);
            Lemmas.Mult_Ge_0 (Element_Type'Pos (D_Next) mod Pow2_LSE_Offset, 2**MSE_Offset);
            declare
               Current : constant Long_Integer := Element_Type'Pos (D_Current) / Pow2_LSE_Offset;
               Next    : constant Long_Integer := Element_Type'Pos (D_Next) mod Pow2_LSE_Offset * 2**MSE_Offset;
            begin
               Result := Result
                 + (Result_Type (Current) + Result_Type (Next))
                 * 2**(Element_Type'Size * Natural (I - Least_Significant_Index));
            end;
         end;
      end loop;

      Result := Result
        + 2**(Element_Type'Size * Natural (Most_Significant_Index - Least_Significant_Index))
        * Result_Type (Element_Type'Pos (D (Most_Significant_Index)) / Pow2_LSE_Offset);
      return Value_Type'Val (Result mod 2**Value_Type'Size);
   end Extract;

   procedure Insert (Value  :        Value_Type;
                     Data   : in out Array_Type;
                     Offset :        Offset_Type)
   is
      pragma Assert (Element_Type'Pos (Element_Type'First) = 0);
      pragma Assert (Element_Type'Pos (Element_Type'Last) = 2**Element_Type'Size - 1);

      LSB_Offset : constant Long_Integer := Offset_Type'Pos (Offset);

      --  Index pointing to least significant element
      Least_Significant_Index : constant Long_Integer := LSB_Offset / Element_Type'Size;

      --  Bits the least significant element (LSE) is shifted left relative to a single element
      LSE_Offset : constant Natural := Natural (LSB_Offset mod Element_Type'Size);

      --  Index pointing to most significant index
      Most_Significant_Index : constant Long_Integer :=
        (LSB_Offset + Long_Integer (Value_Type'Size) - 1) / Element_Type'Size;

      function ES return Natural is (Element_Type'Size) with Post => ES'Result = Element_Type'Size;

      --  Bits of least significant element (LSE)
      LSE_Bits   : constant Natural := Element_Type'Size - LSE_Offset;

      --  Bits of most significant element (MSE)
      MSE_Bits   : constant Natural := (LSE_Offset + Value_Type'Size + Element_Type'Size - 1) mod ES + 1;

      --  Bits the most significant element (MSE) is shifted right relative to a single element
      MSE_Offset : constant Natural := Element_Type'Size - MSE_Bits;

      function Read (Index : Long_Integer) return Element_Type with
        Pre => Index >= 0 and then Index < Data'Length
      is
      begin
         return Data (Index_Type'Val ((Index_Type'Pos (Data'Last) - Index)));
      end Read;

      procedure Write (Index : Long_Integer; Element : Element_Type) with
        Pre => Index >= 0 and then Index < Data'Length
      is
      begin
         Data (Index_Type'Val ((Index_Type'Pos (Data'Last) - Index))) := Element;
      end Write;

      function LIS return Natural is (Long_Integer'Size) with Post => LIS'Result = Long_Integer'Size;
      pragma Assert (2**(LIS - 2) - 1 = 2**(Long_Integer'Size - 2) - 1);
      --  WORKAROUND: Componolit/Workarounds#15
      pragma Annotate (GNATprove, False_Positive, "assertion",
                       "solvers cannot show correspondence between integers and exponentiation abstraction");
      pragma Annotate (GNATprove, False_Positive, "overflow",
                       "solvers cannot show that overflow does not occur for 2**62");

      Pow2_LSE_Offset : constant Long_Integer := 2**LSE_Offset;
      Pow2_LSE_Bits   : constant Long_Integer := 2**LSE_Bits;
      Pow2_ES         : constant Long_Integer := 2**ES;

      pragma Assert (ES < Long_Integer'Size - 2);
      pragma Assert (2**ES = 2**Element_Type'Size);
      --  WORKAROUND: Componolit/Workarounds#15
      pragma Annotate (GNATprove, False_Positive, "assertion",
                       "solvers cannot show correspondence between integers and exponentiation abstraction");
      pragma Annotate (GNATprove, False_Positive, "overflow",
                       "solvers cannot show that overflow does not occur when exponent is lower than (Long_Integer'Size - 2)");

      V : Long_Integer;
   begin
      if Least_Significant_Index = Most_Significant_Index then
         declare
            LR_Value      : constant Long_Integer := Element_Type'Pos (Read (Least_Significant_Index)) mod 2**LSE_Offset;
            Element_Value : constant Long_Integer := (Value_Type'Pos (Value) mod 2**Value_Type'Size);
            UR_Offset     : constant Natural := LSE_Offset + Value_Type'Size;
            UR_Value      : constant Long_Integer := Element_Type'Pos (Read (Most_Significant_Index)) / 2**UR_Offset;
         begin
            Lemmas.Mult_Ge_0 (Element_Value, Pow2_LSE_Offset);
            Lemmas.Mult_Limit (Element_Value, LSE_Bits, Pow2_LSE_Offset, LSE_Offset);
            pragma Assert (Element_Value * Pow2_LSE_Offset <= 2**(LSE_Bits + LSE_Offset));
            --  WORKAROUND: Componolit/Workarounds#15
            pragma Annotate (GNATprove, False_Positive, "assertion",
                             "direct re-expression of lemma postcondition");
            pragma Annotate (GNATprove, False_Positive, "overflow check",
                             "consequence of lemma postcondition");
            Lemmas.Left_Shift_Limit (Element_Value, Value_Type'Size, LSE_Offset);
            Lemmas.Right_Shift_Limit (Element_Type'Pos (Read (Most_Significant_Index)), ES - UR_Offset, UR_Offset);
            Lemmas.Left_Shift_Limit (UR_Value, ES - UR_Offset, UR_Offset);

            Write (Least_Significant_Index, Element_Type'Val (LR_Value + Element_Value * Pow2_LSE_Offset + UR_Value * 2**UR_Offset));
         end;

      else
         --  LSE
         declare
            LSE_Value   : constant Long_Integer := (Value_Type'Pos (Value) mod Pow2_LSE_Bits);
            LSE_Current : constant Long_Integer := Element_Type'Pos (Read (Least_Significant_Index)) mod 2**LSE_Offset;
         begin
            Lemmas.Mult_Ge_0 (LSE_Value, Pow2_LSE_Offset);
            Lemmas.Mult_Limit (LSE_Value, LSE_Bits, Pow2_LSE_Offset, LSE_Offset);
            pragma Assert (LSE_Value * Pow2_LSE_Offset <= 2**(LSE_Bits + LSE_Offset));
            --  WORKAROUND: Componolit/Workarounds#15
            pragma Annotate (GNATprove, False_Positive, "assertion",
                             "direct re-expression of lemma postcondition");
            pragma Annotate (GNATprove, False_Positive, "overflow check",
                             "consequence of lemma postcondition");
            Lemmas.Left_Shift_Limit (LSE_Value, LSE_Bits, LSE_Offset);

            Write (Least_Significant_Index, Element_Type'Val (LSE_Current + LSE_Value * Pow2_LSE_Offset));
            V := Value_Type'Pos (Value) / 2**LSE_Bits;
         end;

         --  LSE + 1 .. MSE - 1
         for I in Least_Significant_Index + 1 .. Most_Significant_Index - 1
         loop
            Write (I, Element_Type'Val (V mod 2**Element_Type'Size));
            V := V / 2**Element_Type'Size;
         end loop;

         --  MSE
         declare
            MSE_Current : constant Long_Integer := Element_Type'Pos (Read (Most_Significant_Index)) / 2**MSE_Bits;
            MSE_Value   : constant Long_Integer := V mod 2**MSE_Bits;
            pragma Assert (MSE_Value < 2**MSE_Bits);
         begin
            Lemmas.Right_Shift_Limit (Element_Type'Pos (Read (Most_Significant_Index)), MSE_Offset, MSE_Bits);
            pragma Assert (2**MSE_Offset <= Natural'Last);
            Lemmas.Left_Shift_Limit (MSE_Current, MSE_Offset, MSE_Bits);
            pragma Assert (MSE_Current * 2**MSE_Bits + MSE_Value <= Element_Type'Pos (Element_Type'Last));

            Write (Most_Significant_Index, Element_Type'Val (MSE_Current * 2**MSE_Bits + MSE_Value));
         end;
      end if;
   end Insert;

end RFLX.Generic_Types;

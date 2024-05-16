pragma SPARK_Mode;

procedure Modular (Arg : Integer)
  with Global => null
is
begin
   case Arg is

      --  Base is over a complete machine integer, 32 bits here

      when 0 .. 9 =>
         declare
            type Base is mod 2**32;
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 10 .. 19 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 20 .. 29 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 20 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 21 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      when 30 .. 39 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 30 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 31 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      --  Base has a binary modulus smaller than a complete machine integer

      when 40 .. 49 =>
         declare
            type Base is mod 128;
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 50 .. 59 =>
         declare
            type Base is mod 128
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 60 .. 69 =>
         declare
            type Base is mod 128
              with Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 60 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 61 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      when 70 .. 79 =>
         declare
            type Base is mod 128
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 70 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 71 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      --  Base has a non-binary modulus

      when 80 .. 89 =>
         declare
            type Base is mod 232;
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 90 .. 99 =>
         declare
            type Base is mod 232
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            B := B + Base'Last; -- @OVERFLOW_CHECK:NONE
            D := D + Der'Last; -- @OVERFLOW_CHECK:NONE
            S := S + Base'Last; -- @OVERFLOW_CHECK:NONE
         end;

      when 100 .. 109 =>
         declare
            type Base is mod 232
              with Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 100 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 101 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      when 110 .. 119 =>
         declare
            type Base is mod 232
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            type Der is new Base;
            subtype Sub is Base range 1 .. 10;
            B : Base := 1;
            D : Der := 5;
            S : Sub := 9;
         begin
            case Arg is
               when 110 =>
                  B := B + Base'Last; -- @OVERFLOW_CHECK:FAIL
               when 111 =>
                  D := D + Der'Last; -- @OVERFLOW_CHECK:FAIL
               when others =>
                  S := S + Base'Last; -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      --  Mix types with annotations or not

      when 120 .. 129 =>
         declare
            type Base is mod 2**32;
            type No_Wrap is mod 2**32
              with Annotate => (GNATprove, No_Wrap_Around);
            type No_Bitwise is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type No_Wrap_No_Bitwise is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            B : Base := Base'Last;
            NW : No_Wrap := No_Wrap'Last;
            NB : No_Bitwise := No_Bitwise'Last;
            NWNB : No_Wrap_No_Bitwise := No_Wrap_No_Bitwise'Last;
         begin
            case Arg is
               when 120 =>
                  B := B + Base(NW) + Base(NB) + Base(NWNB); -- @OVERFLOW_CHECK:NONE
               when 121 =>
                  NW := NW + No_Wrap(B); -- @OVERFLOW_CHECK:FAIL
               when 122 =>
                  NW := NW + No_Wrap(NB); -- @OVERFLOW_CHECK:FAIL
               when 123 =>
                  NW := NW + No_Wrap(NWNB); -- @OVERFLOW_CHECK:FAIL
               when 124 =>
                  NB := No_Bitwise(B) + No_Bitwise(NW) + NB + No_Bitwise(NWNB); -- @OVERFLOW_CHECK:NONE
               when 125 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(B); -- @OVERFLOW_CHECK:FAIL
               when 126 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NW); -- @OVERFLOW_CHECK:FAIL
               when others =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NB); -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      when 130 .. 139 =>
         declare
            type Base is mod 128;
            type No_Wrap is mod 128
              with Annotate => (GNATprove, No_Wrap_Around);
            type No_Bitwise is mod 128
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type No_Wrap_No_Bitwise is mod 128
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            B : Base := Base'Last;
            NW : No_Wrap := No_Wrap'Last;
            NB : No_Bitwise := No_Bitwise'Last;
            NWNB : No_Wrap_No_Bitwise := No_Wrap_No_Bitwise'Last;
         begin
            case Arg is
               when 130 =>
                  B := B + Base(NW) + Base(NB) + Base(NWNB); -- @OVERFLOW_CHECK:NONE
               when 131 =>
                  NW := NW + No_Wrap(B); -- @OVERFLOW_CHECK:FAIL
               when 132 =>
                  NW := NW + No_Wrap(NB); -- @OVERFLOW_CHECK:FAIL
               when 133 =>
                  NW := NW + No_Wrap(NWNB); -- @OVERFLOW_CHECK:FAIL
               when 134 =>
                  NB := No_Bitwise(B) + No_Bitwise(NW) + NB + No_Bitwise(NWNB); -- @OVERFLOW_CHECK:NONE
               when 135 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(B); -- @OVERFLOW_CHECK:FAIL
               when 136 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NW); -- @OVERFLOW_CHECK:FAIL
               when others =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NB); -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      when 140 .. 149 =>
         declare
            type Base is mod 232;
            type No_Wrap is mod 232
              with Annotate => (GNATprove, No_Wrap_Around);
            type No_Bitwise is mod 232
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type No_Wrap_No_Bitwise is mod 232
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            B : Base := Base'Last;
            NW : No_Wrap := No_Wrap'Last;
            NB : No_Bitwise := No_Bitwise'Last;
            NWNB : No_Wrap_No_Bitwise := No_Wrap_No_Bitwise'Last;
         begin
            case Arg is
               when 140 =>
                  B := B + Base(NW) + Base(NB) + Base(NWNB); -- @OVERFLOW_CHECK:NONE
               when 141 =>
                  NW := NW + No_Wrap(B); -- @OVERFLOW_CHECK:FAIL
               when 142 =>
                  NW := NW + No_Wrap(NB); -- @OVERFLOW_CHECK:FAIL
               when 143 =>
                  NW := NW + No_Wrap(NWNB); -- @OVERFLOW_CHECK:FAIL
               when 144 =>
                  NB := No_Bitwise(B) + No_Bitwise(NW) + NB + No_Bitwise(NWNB); -- @OVERFLOW_CHECK:NONE
               when 145 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(B); -- @OVERFLOW_CHECK:FAIL
               when 146 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NW); -- @OVERFLOW_CHECK:FAIL
               when others =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NB); -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      -- Add annotations in derived types

      when 150 .. 169 =>
         declare
            type Base is mod 2**32;
            type No_Wrap is new Base
              with Annotate => (GNATprove, No_Wrap_Around);
            type No_Bitwise is new Base
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type No_Wrap_No_Bitwise is new No_Wrap
              with Annotate => (GNATprove, No_Bitwise_Operations);
            type No_Bitwise_No_Wrap is new No_Bitwise
              with Annotate => (GNATprove, No_Wrap_Around);

            B : Base := Base'Last;
            NW : No_Wrap := No_Wrap'Last;
            NB : No_Bitwise := No_Bitwise'Last;
            NWNB : No_Wrap_No_Bitwise := No_Wrap_No_Bitwise'Last;
            NBNW : No_Bitwise_No_Wrap := No_Bitwise_No_Wrap'Last;
         begin
            case Arg is
               when 150 =>
                  B := B + Base(NW) + Base(NB) + Base(NWNB) + Base(NBNW); -- @OVERFLOW_CHECK:NONE
               when 151 =>
                  NW := NW + No_Wrap(B); -- @OVERFLOW_CHECK:FAIL
               when 152 =>
                  NW := NW + No_Wrap(NB); -- @OVERFLOW_CHECK:FAIL
               when 153 =>
                  NW := NW + No_Wrap(NWNB); -- @OVERFLOW_CHECK:FAIL
               when 154 =>
                  NW := NW + No_Wrap(NBNW); -- @OVERFLOW_CHECK:FAIL
               when 155 =>
                  NB := No_Bitwise(B) + No_Bitwise(NW) + NB + No_Bitwise(NWNB) + No_Bitwise(NBNW); -- @OVERFLOW_CHECK:NONE
               when 156 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(B); -- @OVERFLOW_CHECK:FAIL
               when 157 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NW); -- @OVERFLOW_CHECK:FAIL
               when 158 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NB); -- @OVERFLOW_CHECK:FAIL
               when 159 =>
                  NWNB := NWNB + No_Wrap_No_Bitwise(NBNW); -- @OVERFLOW_CHECK:FAIL
               when 160 =>
                  NBNW := NBNW + No_Bitwise_No_Wrap(B); -- @OVERFLOW_CHECK:FAIL
               when 161 =>
                  NBNW := NBNW + No_Bitwise_No_Wrap(NW); -- @OVERFLOW_CHECK:FAIL
               when 162 =>
                  NBNW := NBNW + No_Bitwise_No_Wrap(NB); -- @OVERFLOW_CHECK:FAIL
               when others =>
                  NBNW := NBNW + No_Bitwise_No_Wrap(NWNB); -- @OVERFLOW_CHECK:FAIL
            end case;
         end;

      -- Other operations than addition

      when 170 .. 179 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations);
            B : Base := 2;
	    Exp : Integer := 35;
         begin
	    case Arg is
	       when 170 =>
		  B := + B; -- @OVERFLOW_CHECK:NONE
	       when 171 =>
		  B := - B; -- @OVERFLOW_CHECK:NONE
	       when 172 =>
		  B := B - Base'Last; -- @OVERFLOW_CHECK:NONE
	       when 173 =>
		  B := B * Base'Last; -- @OVERFLOW_CHECK:NONE
	       when 174 =>
		  B := Base'Last / B; -- @OVERFLOW_CHECK:NONE
	       when 175 =>
		  B := Base'Last mod B; -- @OVERFLOW_CHECK:NONE
	       when 176 =>
		  B := Base'Last rem B; -- @OVERFLOW_CHECK:NONE
	       when 177 =>
		  B := (Base'Last - B) ** 3; -- @OVERFLOW_CHECK:NONE
	       when 178 =>
		  B := B ** Exp; -- @OVERFLOW_CHECK:NONE
	       when others =>
		  B := 2 ** Exp; -- @OVERFLOW_CHECK:NONE
	    end case;
         end;

      when 180 .. 189 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Wrap_Around);
            B : Base := 2;
	    Exp : Integer := 35;
         begin
	    case Arg is
	       when 180 =>
		  B := + B; -- @OVERFLOW_CHECK:NONE
	       when 181 =>
		  B := - B; -- @OVERFLOW_CHECK:FAIL
	       when 182 =>
		  B := B - Base'Last; -- @OVERFLOW_CHECK:FAIL
	       when 183 =>
		  B := B * Base'Last; -- @OVERFLOW_CHECK:FAIL
	       when 184 =>
		  B := Base'Last / B; -- @OVERFLOW_CHECK:NONE
	       when 185 =>
		  B := Base'Last mod B; -- @OVERFLOW_CHECK:NONE
	       when 186 =>
		  B := Base'Last rem B; -- @OVERFLOW_CHECK:NONE
	       when 187 =>
		  B := (Base'Last - B) ** 3; -- @OVERFLOW_CHECK:FAIL
	       when 188 =>
		  B := B ** Exp; -- @OVERFLOW_CHECK:FAIL
	       when others =>
		  B := 2 ** Exp; -- @OVERFLOW_CHECK:FAIL
	    end case;
         end;

      when 190 .. 199 =>
         declare
            type Base is mod 2**32
              with Annotate => (GNATprove, No_Bitwise_Operations),
                   Annotate => (GNATprove, No_Wrap_Around);
            B : Base := 2;
	    Exp : Integer := 35;
         begin
	    case Arg is
	       when 190 =>
		  B := + B; -- @OVERFLOW_CHECK:NONE
	       when 191 =>
		  B := - B; -- @OVERFLOW_CHECK:FAIL
	       when 192 =>
		  B := B - Base'Last; -- @OVERFLOW_CHECK:FAIL
	       when 193 =>
		  B := B * Base'Last; -- @OVERFLOW_CHECK:FAIL
	       when 194 =>
		  B := Base'Last / B; -- @OVERFLOW_CHECK:NONE
	       when 195 =>
		  B := Base'Last mod B; -- @OVERFLOW_CHECK:NONE
	       when 196 =>
		  B := Base'Last rem B; -- @OVERFLOW_CHECK:NONE
	       when 197 =>
		  B := (Base'Last - B) ** 3; -- @OVERFLOW_CHECK:FAIL
	       when 198 =>
		  B := B ** Exp; -- @OVERFLOW_CHECK:FAIL
	       when others =>
		  B := 2 ** Exp; -- @OVERFLOW_CHECK:FAIL
	    end case;
         end;

      when others =>
         null;
   end case;
end;

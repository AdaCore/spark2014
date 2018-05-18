with Ada.Text_IO; use Ada.Text_IO;
with Ada.Unchecked_Conversion;

separate (Skein)
package body Trace
  with SPARK_Mode => Off
is

   Indent : constant String := "    ";

   subtype Perm_Index_4  is U64 range 0 .. 3;

   type Perm_256_Bytes  is array (Perm_Index_4) of Byte_Seq_4;
   type Perm_512_Bytes  is array (Perm_Index_4) of Byte_Seq_8;
   type Perm_1024_Bytes is array (Perm_Index_4) of Byte_Seq_16;

   Perm_256 : constant Perm_256_Bytes :=
     Perm_256_Bytes'(0 => Byte_Seq_4'(0, 1, 2, 3),
                     1 => Byte_Seq_4'(0, 3, 2, 1),
                     2 => Byte_Seq_4'(0, 1, 2, 3),
                     3 => Byte_Seq_4'(0, 3, 2, 1));

   Perm_512 : constant Perm_512_Bytes :=
     Perm_512_Bytes'(0 => Byte_Seq_8'(0, 1, 2, 3, 4, 5, 6, 7),
                     1 => Byte_Seq_8'(2, 1, 4, 7, 6, 5, 0, 3),
                     2 => Byte_Seq_8'(4, 1, 6, 3, 0, 5, 2, 7),
                     3 => Byte_Seq_8'(6, 1, 0, 7, 2, 5, 4, 3));

   Perm_1024 : constant Perm_1024_Bytes :=
     Perm_1024_Bytes'(0 => Byte_Seq_16'(0,  1, 2,  3, 4,  5, 6,  7,
                                        8,  9, 10, 11, 12, 13, 14, 15),
                      1 => Byte_Seq_16'(0,  9, 2, 13, 6, 11, 4, 15,
                                        10,  7, 12,  3, 14,  5,  8,  1),
                      2 => Byte_Seq_16'(0,  7, 2,  5, 4,  3, 6,  1,
                                        12, 15, 14, 13,  8, 11, 10,  9),
                      3 => Byte_Seq_16'(0, 15, 2, 11, 6, 13, 4,  9,
                                        14,  1,  8,  5, 10,  3, 12,  7));

   package U64_IO  is new Ada.Text_IO.Modular_IO (U64);
   package U32_IO  is new Ada.Text_IO.Modular_IO (U32);

   Flags : Skein.Debug_Flag_Set := Skein.Debug_None;

   Inject_Num : Natural := 0;

   subtype String_2_Index is Positive range 1 .. 2;
   subtype String_6_Index is Positive range 1 .. 6;
   subtype String_2 is String (String_2_Index);
   subtype String_6 is String (String_6_Index);

   --  Image of injection count, two digits with leading space if less than 10
   --  mimics C's printf %2d format.
   function Round_Image (R : in U64) return String_2;

   function Round_Image (R : in U64) return String_2
   is
      S : constant String := U64'Image (R);
   begin
      if R < 10 then
         return ' ' & S (2);
      elsif R > 99 then
         return "--";
      else
         return String_2 (S (2 .. 3));
      end if;
   end Round_Image;

   --  Image of injection count, two digits with leading zeroes - mimics C's
   --  printf %02d format.
   function Inject_Image (I : in Natural) return String_2;

   function Inject_Image (I : in Natural) return String_2
   is
      S : constant String := Natural'Image (I);
   begin
      if I < 10 then
         return '0' & S (2);
      elsif I > 99 then
         return "--";
      else
         return String_2 (S (2 .. 3));
      end if;
   end Inject_Image;

   --  Image of T0, six digits with leading zeroes - mimics C's
   --  printf %06X format.
   function T0_Image (T0 : in U64) return String_6;

   function T0_Image (T0 : in U64) return String_6
   is
      Result : String_6 := "000000";
      C : String (1 .. 20); -- enough for "16#aabbccddeeffgghh#"
      LSB_Index : Positive := 19;
   begin
      U64_IO.Put (C, T0, 16);
      for I in reverse String_6_Index loop
         Result (I) := C (LSB_Index);
         LSB_Index := LSB_Index - 1;
         exit when C (LSB_Index) = '#';
      end loop;

      return Result;
   end T0_Image;

   procedure Set_Flags (F : in Debug_Flag_Set)
   is
   begin
      Flags := F;
   end Set_Flags;

   procedure Put_Byte (B : in Byte);

   procedure Put_Byte (B : in Byte)
   is
      subtype Nibble is Byte range 0 .. 15;
      type Nibble_To_Char is array (Nibble) of Character;
      To_Char : constant Nibble_To_Char :=
        Nibble_To_Char'('0', '1', '2', '3', '4', '5', '6', '7',
                        '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
      MSB : constant Nibble := B / 16;
      LSB : constant Nibble := B mod 16;
   begin
      Put (Standard_Output, To_Char (MSB));
      Put (Standard_Output, To_Char (LSB));
   end Put_Byte;

   procedure Put_Word_32 (W : in U32);

   procedure Put_Word_32 (W : in U32)
   is
      B1 : constant Byte := Byte ((W / 2**24) mod 256);
      B2 : constant Byte := Byte ((W / 2**16) mod 256);
      B3 : constant Byte := Byte ((W /  2**8) mod 256);
      B4 : constant Byte := Byte (W mod 256);
   begin
      Put_Byte (B1);
      Put_Byte (B2);
      Put_Byte (B3);
      Put_Byte (B4);
   end Put_Word_32;


   procedure Show_64 (S     : in U64_Seq;
                      Count : in U64)
   is
   begin

      if Count >= 1 then
         for I in U64 range S'First .. Count - 1 loop
            if (I mod 4) = 0 then
               Put (Indent);
            end if;

            Put (' ');
            Put_Word_32 (U32 (Interfaces.Shift_Right (S (I), 32)));
            Put ('.');
            Put_Word_32 (U32 (S (I) and 16#FFFF_FFFF#));
            Put (' ');
            if ((I mod 4) = 3) or I = S'Last then
               New_Line;
            end if;

         end loop;
      end if;
   end Show_64;

   procedure Show_Msg_64 (Msg   : in String;
                          S     : in U64_Seq;
                          Count : in U64)
   is
   begin
      Put_Line (Msg);
      Show_64 (S, Count);
      New_Line;
   end Show_Msg_64;

   procedure Show_8 (S     : in Byte_Seq;
                     Count : in U64)
   is
   begin

      if Count >= 1 then
         for I in U64 range S'First .. Count - 1 loop
            if (I mod 16) = 0 then
               Put (Indent);
            else
               if (I mod 4) = 0 then
                  Put (' ');
               end if;
            end if;

            Put (' ');
            Put_Byte (S (I));

            if (I mod 16) = 15 or I = S'Last then
               New_Line;
            end if;
         end loop;
      end if;
   end Show_8;

   procedure Show_Msg_8 (Msg   : in String;
                         S     : in Byte_Seq;
                         Count : in U64)
   is
   begin
      Put_Line (Msg);
      Show_8 (S, Count);
      New_Line;
   end Show_Msg_8;


   function Algorithm_Header (Bits : in Bit_Size) return String;

   function Algorithm_Header (Bits : in Bit_Size) return String
   --# global in Flags;
   is
   begin
      if Flags (ThreeFish) then
         case Bits is
            when S256 =>
               return ":Threefish-256: ";
            when S512 =>
               return ":Threefish-512: ";
            when S1024 =>
               return ":Threefish-1024:";
         end case;
      else
         case Bits is
            when S256 =>
               return ":Skein-256: ";
            when S512 =>
               return ":Skein-512: ";
            when S1024 =>
               return ":Skein-1024:";
         end case;
      end if;
   end Algorithm_Header;

   procedure Show_Final
     (Bits         : in Skein.Bit_Size;
      H            : in Skein.Context_Header;
      Block        : in Byte_Seq;
      Byte_Count   : in U64;
      Block_Offset : in U64)
   is
   begin
      if Flags (Config) or
        H.Tweak_Words.Field_Type /= Skein_Block_Type_Cfg then
         if Flags (Final) then
            New_Line;
            Put_Line (Algorithm_Header (Bits) & " Final output=");

            if Byte_Count > 0 then
               declare
                  subtype Result_Block_Index is U64 range 0 .. Byte_Count - 1;
                  subtype Result_Block is Byte_Seq (Result_Block_Index);
               begin
                  --  Slice and slide to meet precondition of Show_8
                  Show_8
                    (Result_Block
                       (Block (Block'First + Block_Offset ..
                                 Block'First + Block_Offset + Byte_Count - 1)),
                     Byte_Count);
               end;
            end if;

            Put_Line ("    ++++++++++");
         end if;
      end if;
   end Show_Final;

   procedure Show_Round
     (Bits : in Bit_Size;
      H    : in Context_Header;
      R    : in U64;
      X    : in U64_Seq)
   is
   begin
      if Flags (Config) or
        H.Tweak_Words.Field_Type /= Skein_Block_Type_Cfg then
         if Flags /= Debug_None then

            if R >= Skein_Rnd_Special then
               --  a key injection (or feedforward) point
               if R = Skein_Rnd_Key_Initial then
                  Inject_Num := 0;
               else
                  Inject_Num := Inject_Num + 1;
               end if;

               if Flags (Inject) or
                 (Flags (Final) and R = Skein_Rnd_Feed_Fwd) then
                  New_Line;
                  Put (Algorithm_Header (Bits));
                  case R is
                     when Skein_Rnd_Key_Initial =>
                        Put (" [state after initial key injection]");

                     when Skein_Rnd_Key_Inject  =>
                        Put (" [state after key injection #" &
                               Inject_Image (Inject_Num) & "]");

                     when Skein_Rnd_Feed_Fwd    =>
                        Put (" [state after plaintext feedforward]");
                        Inject_Num := 0;
                     when others =>
                        null;
                  end case;
                  Put ('=');
                  New_Line;
                  Show_64 (X, X'Length);
                  if (R = Skein_Rnd_Feed_Fwd) then
                     Put ("    ----------");
                     New_Line;
                  end if;

               end if;

            elsif Flags (Rounds) then
               if Flags (Permute) and (R and 3) /= 0 then
                  New_Line;
                  Put_Line (Algorithm_Header (Bits) &
                              " [state after round " &
                              Round_Image (R) & " (permuted)]=");
                  case Bits is
                     when S256 =>
                        declare
                           Perm : Byte_Seq_4;
                           P    : U64_Seq_4;
                        begin
                           Perm := Perm_256 (R and 3);
                           for J in I4 loop
                              P (J) := X (U64 (Perm (J)));
                           end loop;
                           Show_64 (P, P'Length);
                        end;
                     when S512 =>
                        declare
                           Perm : Byte_Seq_8;
                           P    : U64_Seq_8;
                        begin
                           Perm := Perm_512 (R and 3);
                           for J in I8 loop
                              P (J) := X (U64 (Perm (J)));
                           end loop;
                           Show_64 (P, P'Length);
                        end;
                     when S1024 =>
                        declare
                           Perm : Byte_Seq_16;
                           P    : U64_Seq_16;
                        begin
                           Perm := Perm_1024 (R and 3);
                           for J in I16 loop
                              P (J) := X (U64 (Perm (J)));
                           end loop;
                           Show_64 (P, P'Length);
                        end;
                  end case;
               else
                  New_Line;
                  Put_Line (Algorithm_Header (Bits) &
                              " [state after round " &
                              Round_Image (R) & "]=");
                  Show_64 (X, X'Length);
               end if;
            end if;


         end if;
      end if;

   end Show_Round;


   procedure Show_Block
     (Bits         : in Bit_Size;
      H            : in Context_Header;
      X            : in U64_Seq;
      Block        : in Byte_Seq;
      Block_Offset : in U64;
      W            : in U64_Seq;
      KS           : in U64_Seq;
      TS           : in U64_Seq)
   is
      function Tweak_To_Words is new Ada.Unchecked_Conversion
        (Tweak_Value, Modifier_Words);
   begin
      if Flags (Config) or
        H.Tweak_Words.Field_Type /= Skein_Block_Type_Cfg then
         if Flags /= Debug_None then

            if Flags (Header) then
               New_Line;
               Put (Algorithm_Header (Bits) & " Block: outBits=");
               U64_IO.Put (Item => H.Hash_Bit_Len, Width => 4, Base => 10);
               Put (". T0=" &
                      T0_Image (H.Tweak_Words.Byte_Count_LSB) &
                      ". Type=");
               case H.Tweak_Words.Field_Type is
                  when Skein_Block_Type_Key   =>
                     Put ("KEY. ");
                  when Skein_Block_Type_Cfg   =>
                     Put ("CFG. ");
                  when Skein_Block_Type_Pers  =>
                     Put ("PERS.");
                  when Skein_Block_Type_PK    =>
                     Put ("PK.  ");
                  when Skein_Block_Type_KDF   =>
                     Put ("KDF. ");
                  when Skein_Block_Type_Msg   =>
                     Put ("MSG. ");
                  when Skein_Block_Type_Out   =>
                     Put ("OUT. ");
                  when others               =>
                     Put ("0x");
                     Put_Byte (Byte (H.Tweak_Words.Field_Type));
                     Put ('.');
               end case;
               Put (" Flags=");
               if H.Tweak_Words.First_Block then
                  Put (" First");
               else
                  Put ("      ");
               end if;
               if H.Tweak_Words.Final_Block then
                  Put (" Final");
               else
                  Put ("      ");
               end if;
               if H.Tweak_Words.Bit_Pad then
                  Put (" Pad");
               else
                  Put ("    ");
               end if;
               if H.Tweak_Words.Tree_Level /= 0 then
                  Put ("  TreeLevel = ");
                  Put_Byte (Byte (H.Tweak_Words.Tree_Level));
               end if;
               New_Line;
            end if;

            if Flags (Tweak) then
               Put ("  Tweak:");
               New_Line;
               Show_64 (Tweak_To_Words (H.Tweak_Words),
                        Skein_Modifier_Words_C);
            end if;

            if Flags (State) then
               if Flags (ThreeFish) then
                  Put ("  Key words:");
               else
                  Put ("  State words:");
               end if;
               New_Line;
               Show_64 (X, X'Length);
            end if;

            if Flags (Key_Sched) then
               Put_Line ("  Tweak schedule:");
               Show_64 (TS, TS'Length);
               Put_Line ("  Key   schedule:");
               Show_64 (KS, KS'Length);
            end if;

            if Flags (Input_64) then
               Put_Line ("  Input block (words):");
               Show_64 (W, W'Length);
            end if;

            if Flags (Input_08) then
               Put_Line ("  Input block (bytes):");
               --  Slice and slide to meet precondition of Show_8
               Show_8 (Byte_Seq (Block (Block_Offset .. Block'Last)),
                       W'Length * 8);
            end if;

         end if;

      end if;
   end Show_Block;

   procedure Show_Key
     (Bits      : in Skein.Bit_Size;
      H         : in Skein.Context_Header;
      Key_Bytes : in Byte_Seq)
   is
   begin
      if Key_Bytes'Length > 0 then
         if Flags (Config) or
           H.Tweak_Words.Field_Type /= Skein_Block_Type_Cfg then
            if Flags (Key) then
               New_Line;
               Put (Algorithm_Header (Bits) & " MAC key = ");
               U32_IO.Put (Item => Key_Bytes'Length, Width => 4, Base => 10);
               Put_Line (" bytes");
               Show_8 (Key_Bytes, Key_Bytes'Length);
            end if;
         end if;
      end if;
   end Show_Key;

end Trace;

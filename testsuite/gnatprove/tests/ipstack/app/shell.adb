------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2017, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

pragma Ada_2005;

with AIP.ARP;
with AIP.Nif;
with AIP.IO;
with AIP.IPaddrs;

package body Shell is

   type Shell_State is
     (Prompt,     --  Shell must prompt for next command
      Waiting,    --  Waiting for command
      Running,    --  Command running
      Completed); --  Command completed

   State : Shell_State := Prompt;
   --  Shell state

   Cmd_Val : Integer := 0;
   --  Command return value

   PS : constant String := "IPstack> ";

   function Image (A : AIP.IPaddrs.IPaddr) return String;
   --  Return dotted quad representation of A

   procedure Parse
     (DQ  : String;
      A   : out AIP.IPaddrs.IPaddr;
      Err : out AIP.Err_T);
   --  Parse dotted quad into address

   function Starts_With (S, Prefix : String) return Boolean;
   --  True if S starts with Prefix

   -----------
   -- Image --
   -----------

   function Image (A : AIP.IPaddrs.IPaddr) return String is
      use AIP, AIP.IPaddrs;

      AA     : IPaddr := A;
      B      : M8_T;
      Result : String (1 .. 15);
      Index  : Integer := Result'Last;

   begin
      for J in 1 .. 4 loop
         B := M8_T (AA and 16#ff#);
         for K in 0 .. 2 loop
            Result (Index) := Character'Val (Character'Pos ('0') + B mod 10);
            Index := Index - 1;
            B := B / 10;
            exit when B = 0;
         end loop;

         if J < 4 then
            Result (Index) := '.';
            Index := Index - 1;
         end if;
         AA := AA / 256;
      end loop;
      return Result (Index + 1 .. Result'Last);
   end Image;

   -----------
   -- Parse --
   -----------

   procedure Parse
     (DQ  : String;
      A   : out AIP.IPaddrs.IPaddr;
      Err : out AIP.Err_T)
   is
      use AIP, AIP.IPaddrs;

      D : Boolean;
      --  True if a digit has been seen for the current byte

      B : M8_T;
      --  Current byte value being constructed

      Dots : U8_T;
      --  How many dots found

   begin
      A := 0;
      Err := ERR_VAL;
      D := False;
      B := 0;
      Dots := 0;

      for J in DQ'Range loop
         case DQ (J) is
            when '0' .. '9' =>
               D := True;
               B := B * 10 + Character'Pos (DQ (J)) - Character'Pos ('0');
            when '.' =>
               if not D or else Dots = 3 then
                  return;
               end if;
               Dots := Dots + 1;
               A := A * 256 + IPaddr (B);
               D := False;
               B := 0;
            when others =>
               return;
         end case;
      end loop;

      if not D or else Dots /= 3 then
         return;
      end if;
      A := A * 256 + IPaddr (B);
      Err := NOERR;
   end Parse;

   ----------
   -- Poll --
   ----------

   procedure Poll is
   begin
      if State = Completed then
         AIP.IO.Put_Line ("STATUS =" & Cmd_Val'Img);
         State := Prompt;
      end if;

      if State = Prompt then
         AIP.IO.Put (PS);
         State := Waiting;
      end if;

      if State = Waiting and then AIP.IO.Line_Available then
         declare
            Line : String renames AIP.IO.Line (1 .. AIP.IO.Get_Last);
         begin
            if Line = "if list" then
               declare
                  subtype If_Name_T is String (1 .. 2);
                  type If_Name_Acc is access all If_Name_T;
                  function Get_Netif
                    (Nid : AIP.Nif.Netif_Id) return If_Name_Acc;
                  pragma Import (Ada, Get_Netif, "AIP_get_netif");

                  If_Name : If_Name_Acc;
               begin
                  for J in AIP.Nif.Netif_Id'Range loop
                     If_Name := Get_Netif (J);
                     exit when If_Name (1) = ' ';
                     AIP.IO.Put (If_Name.all & ' ');
                     AIP.IO.Put (AIP.Nif.NIF_State (J)'Img & ' ');
                     AIP.IO.Put_Line (Image (AIP.Nif.NIF_Addr (J)));
                  end loop;
               end;
               State := Completed;
               Cmd_Val := 0;

            elsif Starts_With (Line, "if config ") then
               declare
                  use AIP, AIP.IPaddrs, AIP.Nif;

                  First, Last : Integer;
                  --  Indices of first and last character of current word

                  Word : Integer;
                  --  Index of current word

                  I    : AIP.EID;
                  --  Interface identifier

                  A, M : IPaddr;
                  --  Address and netmask

                  E    : Err_T;
                  --  Error status returned by If_Config call

               begin
                  Word := 0;
                  First := 11;
                  E := NOERR;

                  while First <= Line'Last loop
                     Last := First;
                     while Last <= Line'Last and then Line (Last) /= ' ' loop
                        Last := Last + 1;
                     end loop;
                     Last := Last - 1;

                     case Word is
                        when 0 =>
                           I := 0;
                           for J in First .. Last loop
                              I := I * 10
                                + Character'Pos (Line (J))
                                - Character'Pos ('0');
                           end loop;
                           E := NOERR;
                        when 1 =>
                           Parse (Line (First .. Last), A, E);
                        when 2 =>
                           if Last = Line'Last then
                              Parse (Line (First .. Last), M, E);
                           else
                              E := ERR_VAL;
                           end if;
                        when others =>
                           E := ERR_VAL;
                     end case;
                     exit when E /= NOERR;

                     First := Last + 2;
                     Word := Word + 1;
                  end loop;

                  if E = NOERR then
                     AIP.Nif.If_Config
                       (Nid       => I,
                        IP        => A,
                        Mask      => M,
                        Broadcast => (A and M) or (not M),
                        Remote    => 0,
                        Err       => E);
                  end if;
                  Cmd_Val := Integer (E);
                  State := Completed;
               end;

            elsif Line = "arp clear" then
               AIP.ARP.ARP_Clear;
               State := Completed;
               Cmd_Val := 0;

            elsif Starts_With (Line, "parse ") then
               declare
                  use AIP, AIP.IPaddrs;

                  A : IPaddr;
                  E : Err_T;

               begin
                  Parse (Line (7 .. Line'Last), A, E);
                  if E = NOERR then
                     AIP.IO.Put_Line ("ADDR = " & Image (A));
                  end if;
                  Cmd_Val := Integer (E);
                  State := Completed;
               end;

            elsif Line = "exit" then
               raise Program_Error with "user requested exit";

            else
               AIP.IO.Put_Line ("bad command: " & Line);
               State := Completed;
               Cmd_Val := 1;
            end if;
         end;
      end if;
   end Poll;

   -----------------
   -- Starts_With --
   -----------------

   function Starts_With (S, Prefix : String) return Boolean is
   begin
      return S'Length >= Prefix'Length
               and then
             S (S'First .. S'First + Prefix'Length - 1) = Prefix;
   end Starts_With;

end Shell;

------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
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

   -----------
   -- Image --
   -----------

   function Image (A : AIP.IPaddrs.IPaddr) return String is
      use type AIP.IPaddrs.IPaddr;
      AA     : AIP.IPaddrs.IPaddr := A;
      B      : AIP.IPaddrs.IPaddr;
      Result : String (1 .. 15);
      Index  : Integer := Result'Last;

   begin
      for J in 1 .. 4 loop
         B := AA and 16#ff#;
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
            Line : constant String := AIP.IO.Get;
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

            elsif Line = "arp clear" then
               AIP.ARP.ARP_Clear;
               State := Completed;
               Cmd_Val := 0;

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

end Shell;

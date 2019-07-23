package body P is
   procedure Effect1 (B : Boolean; E : Single; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when One =>
            if B then
               Y := Single'Pos (E);
            end if;
--         when others =>
--            raise Program_Error;
      end case;
   end Effect1;

   procedure Effect2 (B : Boolean; E : Single; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      if E = One and then B then
         Y := Single'Pos (E);
      end if;
   end Effect2;
end P;

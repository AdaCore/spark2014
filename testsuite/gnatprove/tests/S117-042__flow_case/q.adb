package body Q is
   procedure Effect1 (B : Boolean; E : Single1; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when One =>
            if B then
               Y := Single1'Pos (E);
            end if;
      end case;
   end Effect1;

   procedure Effect2 (B : Boolean; E : Single2; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when Two =>
            if B then
               Y := Single2'Pos (E);
            end if;
      end case;
   end Effect2;

   procedure Effect3 (B : Boolean; E : Single3; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when Three =>
            if B then
               Y := Single3'Pos (E);
            end if;
      end case;
   end Effect3;

   procedure Effect4 (B : Boolean; E : Single4; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when One =>
            if B then
               Y := Single4'Pos (E);
            end if;
      end case;
   end Effect4;

   procedure Effect5 (B : Boolean; E : Single5; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when Two =>
            if B then
               Y := Single5'Pos (E);
            end if;
      end case;
   end Effect5;

   procedure Effect6 (B : Boolean; E : Single6; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when Three =>
            if B then
               Y := Single6'Pos (E);
            end if;
      end case;
   end Effect6;

   procedure Effect0 (B : Boolean; E : Triple; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case Single3'(E) is
         when Three =>
            if B then
               Y := Triple'Pos (E);
            end if;
      end case;
   end Effect0;

   procedure Effect7 (B : Boolean; E : Triple; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when others =>
            if B then
               Y := Triple'Pos (E);
            end if;
      end case;
   end Effect7;

   procedure EffectD (B : Boolean; E : Triple; Y : out Integer) is
   begin
      Y := 0;  -- a default value

      case E is
         when others =>
            if B then
               Y := 12345;
            end if;
      end case;
   end EffectD;
end Q;

package body P is

   procedure Get (X : Integer; Y : out T) is
   begin
      Y := (Valid => True, C => <>);

      case X is
         when 0 =>
            Y.C := 1;

         when others =>
            Y := (Valid => False);
      end case;
   end;

end;

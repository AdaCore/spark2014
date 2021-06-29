procedure Main with SPARK_Mode is
   type Enum is (A, B);

   procedure Call is null;

   procedure Dead_Loop (Value : Enum) is
   begin
      for I in 1 .. 0 loop
         case Value is
            when A  => null;
            when B  => Call; raise Program_Error;
         end case;
         null;
      end loop;
   end Dead_Loop;

   procedure Dead_Return (Value : Enum) is
   begin
      return;
      case Value is
         when A  => null;
         when B  => Call; raise Program_Error;
      end case;
      null;
   end Dead_Return;

   procedure Dead_Goto (Value : Enum) is
   begin
      goto L1;
      case Value is
         when A  => null;
         when B  => Call; raise Program_Error;
      end case;
      null;
      <<L1>>
   end Dead_Goto;


begin
   null;
end Main;

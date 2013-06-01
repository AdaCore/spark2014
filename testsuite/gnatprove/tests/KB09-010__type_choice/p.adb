package body P is
   function F (X : Any_Priority) return Integer is
   begin
      case X is
	 when Interrupt_Priority              => return 15;
	 when Priority'First .. Priority'Last => return 6;
      end case;
   end F;
end P;

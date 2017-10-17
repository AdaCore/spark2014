package body Case_Assign is
  procedure Assign (X : out Integer; Y : in Integer; Op : in Oper) is
  begin
     case Op is
        when Incr =>
           X := Y + 1;
        when Decr =>
           X := Y - 1;
        when Double =>
           X := Y * 2;
     end case;
  end Assign;
end Case_Assign;

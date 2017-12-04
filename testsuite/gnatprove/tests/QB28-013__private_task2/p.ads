package P is
   type TT is limited private;
   type PT is limited private;
private
   task type TT;
   protected type PT is end;
end;

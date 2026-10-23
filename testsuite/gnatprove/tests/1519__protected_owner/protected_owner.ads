package Protected_Owner with SPARK_Mode is
   type Int_Access is access Integer;
   protected type Cell is
      procedure Inner;
      procedure Outer;
   private
      P : Int_Access := null;
   end Cell;
end Protected_Owner;

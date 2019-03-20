package body Simple
  with SPARK_Mode
is
   protected P is
      function Is_Set return Boolean;
      procedure Toggle
      with Post => (Is_Set = not Is_Set'Old);
   private
      State : Boolean := False;
   end P;

   protected body P is
      function Is_Set return Boolean is (State);

      procedure Toggle is
      begin
         State := not State;
      end Toggle;
   end P;
end Simple;

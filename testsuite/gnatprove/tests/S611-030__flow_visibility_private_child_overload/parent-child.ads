package Parent.Child is
   type Auto_Speed is new Remote_Camera with private;

private
   type Film_Speed is (One_Hundred, Two_Hundred);
   type Auto_Speed is new Remote_Camera with record
      ASA : Film_Speed;
   end record;
   procedure Focus (C : in out Auto_Speed);
end Parent.Child;

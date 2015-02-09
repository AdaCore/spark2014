package Parent is
   type Root_T is tagged private;

   procedure Initialize (R : out Root_T);
private
   type Root_T is tagged record
      X : Integer;
   end record;
end Parent;

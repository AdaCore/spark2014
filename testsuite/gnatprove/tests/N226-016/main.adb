with Sink;

procedure Main
with
   Global  => (Output        => Sink.The_Sink),
   Depends => (Sink.The_Sink => null)
is
   subtype Id_Type is Natural range 0 .. 1;
   type Map_Type is array (Id_Type) of Id_Type;
   Map : constant Map_Type := Map_Type'(0 => 1, 1 => 0);

   function With_Postcondition
     (Id : Id_Type)
      return Id_Type
   with
      Global => null,
      Post   => (Id /= With_Postcondition'Result)
   is
   begin
      return Map (Id);
   end With_Postcondition;

   function With_Invariant
     (Id : Id_Type)
      return Id_Type
   with
      Global => null,
      Post   => (Id /= With_Invariant'Result)
   is
   begin
      pragma Assert (for all Id in Id_Type => (Map (Id) /= Id));
      return Map (Id);
   end With_Invariant;

   function With_Spoon_Feeding
     (Id : Id_Type)
      return Id_Type
   with
      Global => null,
      Post   => (Id /= With_Spoon_Feeding'Result)
   is
   begin
      pragma Assert (Map (0) = 1 and Map (1) = 0);
      pragma Assert (for all Id in Id_Type => (Map (Id) /= Id));
      return Map (Id);
   end With_Spoon_Feeding;
begin
   Sink.The_Sink := With_Postcondition (1);
   Sink.The_Sink := With_Invariant (1);
   Sink.The_Sink := With_Spoon_Feeding (1);
end Main;



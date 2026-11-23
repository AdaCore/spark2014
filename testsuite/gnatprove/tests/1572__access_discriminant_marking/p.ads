package P is
   type T (Element : not null access Integer) is limited null record;

   type With_Default (Element : access Integer := null) is limited null record;

   type Constrained_Parent (Element : access Integer; Count : Integer)
     is limited null record;
   type Derived is new Constrained_Parent (null, 1);

   protected type Protected_Type (Element : access Integer := null) is
      procedure Touch;
   private
      Value : Integer := 0;
   end Protected_Type;
end P;

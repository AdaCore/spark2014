package Parent.Public1.Public2 is
   A : Parent_Int;
   type Another is private;
   procedure Modify (Value : in out Another);
private
   type Another is new Pub_Array1;
end Parent.Public1.Public2;

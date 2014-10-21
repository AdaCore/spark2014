package Tagged_DIC is
   type Root is tagged private
     with Default_Initial_Condition;

   function Gimme_One return Root;

   type Root_2 is tagged private;

   function Gimme_One return Root_2;
private
   type Root is tagged record
      X : Integer := 0;
   end record;

   type Root_2 is tagged record
      X : Integer;
   end record;
end Tagged_DIC;

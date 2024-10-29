package Types with SPARK_Mode is
   package Par is
      type Root is tagged record I : Integer; end record;
   end Par;

   package Chi is
      type Child is new Par.Root with record J : Integer; end record;

      function "=" (Left, Right : Child) return Boolean with Post => false;

      G : Child := Child'(I => 0, J => 0);
   end Chi;
end Types;

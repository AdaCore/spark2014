package body IandATypes
is
   function "+"(X : TemplateT ; Y : TemplateT) return TemplateT
   is
   begin
      return (TemplateT (Integer(X) + Integer (Y)));
   end "+";
end IandATypes;

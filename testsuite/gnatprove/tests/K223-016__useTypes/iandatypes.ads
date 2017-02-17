
package IandATypes
is
   type TemplateT is new Integer range 1 .. 10;
   function "+"(X : TemplateT ; Y : TemplateT) return TemplateT;
end IandATypes;

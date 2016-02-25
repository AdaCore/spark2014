with Gen2;

generic
   X : in out Integer;
package Gen1 is
   package Inst2 is new Gen2 (X);
end;

generic
   K : Integer;
package Gen_Exc is
   Bad : exception;
   Too_Bad : exception renames Bad;
end Gen_Exc;

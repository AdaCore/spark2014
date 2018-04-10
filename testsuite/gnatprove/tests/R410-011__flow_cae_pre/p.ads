with Other;

package P is
   protected type PT is
      entry E with Pre => Other.Read_Hidden_CAE;
   end;
end;

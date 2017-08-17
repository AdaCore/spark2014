with Addr;
package P is
   procedure Subp
     with Import,
          Address => Addr.F;
end;

with Gen_Unit;
package P is

   generic function Generic_Proxy return Integer;

   package Unit is new Gen_Unit;
end;

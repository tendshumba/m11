ConstructClass := function(P, N, x: Limit := 3^12)
   Cx := {P | x};
   repeat
      Include(~Cx, x^Random(N));
   until #Cx eq Limit;
   return Cx;
end function;

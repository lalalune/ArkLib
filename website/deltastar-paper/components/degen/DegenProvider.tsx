"use client";

import {
  createContext,
  useCallback,
  useContext,
  useEffect,
  useState,
  type ReactNode,
} from "react";

type DegenCtx = {
  degen: boolean;
  toggle: () => void;
};

const Ctx = createContext<DegenCtx>({ degen: false, toggle: () => {} });

export function useDegen() {
  return useContext(Ctx);
}

export function DegenProvider({ children }: { children: ReactNode }) {
  const [degen, setDegen] = useState(false);

  useEffect(() => {
    try {
      if (localStorage.getItem("deltastar-degen") === "1") setDegen(true);
    } catch {}
  }, []);

  const toggle = useCallback(() => {
    setDegen((d) => {
      const next = !d;
      try {
        localStorage.setItem("deltastar-degen", next ? "1" : "0");
      } catch {}
      return next;
    });
  }, []);

  return <Ctx.Provider value={{ degen, toggle }}>{children}</Ctx.Provider>;
}

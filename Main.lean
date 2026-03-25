import Std.Data.HashMap
import VersoManual
import SutherlandNumberTheory

open Verso.Genre Manual

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc SutherlandNumberTheory) (config := config)

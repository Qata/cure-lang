defmodule Cure.Diagnostic.Adapter.Macro do
  @moduledoc """
  Converts authored macro-family and expansion failures.

  Generated implementation details remain in payloads and provenance; primary
  labels point at authored macro syntax whenever a source span is available.
  """

  alias Cure.Diagnostic

  alias Cure.Diagnostic.{
    Doc,
    Label,
    ProvenanceFrame,
    Span,
    Suggestion,
    TextEdit
  }

  alias Cure.Diagnostic.Suggest

  @spec from_error(term(), keyword()) :: Diagnostic.t()
  def from_error(error, opts \\ [])

  def from_error({:unknown_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_syntax_family_field,
      severity: :error,
      title: "Unknown syntax-family field",
      body: Doc.paragraph("`#{details.field}` is not a field of the `#{details.family}` syntax family."),
      primary:
        label(
          span,
          :primary,
          "this field is not declared by the family"
        ),
      suggestions: syntax_family_field_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:missing_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :missing_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is missing",
      body: Doc.paragraph("The `#{details.family}` syntax family requires a `#{details.field}` section here."),
      primary: label(span, :primary, "add `#{details.field}` here"),
      suggestions: [
        %Suggestion{
          message: "Add a `#{details.field} ...` section to this family body",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:unknown_macro_obligation_capture, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    Diagnostic.new(
      code: "E092",
      key: :unknown_macro_obligation_capture,
      severity: :error,
      title: "Unknown macro capture",
      body:
        Doc.paragraph(
          "The `#{details.interface}` obligation refers to `#{details.capture}`, but this rule declares no capture with that name."
        ),
      primary:
        label(
          span,
          :primary,
          "this capture is not declared by the rule"
        ),
      suggestions: macro_capture_suggestions(details, span),
      payload: details
    )
  end

  def from_error({:unit_type_reserved, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :unit_span),
             :secondary,
             "this spelling denotes the built-in `Unit` type"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :unit_type_reserved,
      severity: :error,
      title: "Unit syntax cannot define another type",
      body: Doc.paragraph("`()` has exactly one type, `Unit`, so it cannot define the new type `#{details.name}`."),
      primary:
        label(
          span,
          :primary,
          "this declaration must not reuse `Unit` syntax"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Give `#{details.name}` its own constructor, or rename the type to `Unit`",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({:duplicate_syntax_family_field, details}, opts)
      when is_map(details) do
    span = Map.get(details, :span) || Keyword.get(opts, :span)

    secondary =
      case label(
             Map.get(details, :first_span),
             :secondary,
             "the field was first supplied here"
           ) do
        nil -> []
        related -> [related]
      end

    Diagnostic.new(
      code: "E092",
      key: :duplicate_syntax_family_field,
      severity: :error,
      title: "Syntax-family field is duplicated",
      body: Doc.paragraph("The `#{details.field}` field may be supplied only once in this family body."),
      primary:
        label(
          span,
          :primary,
          "this second `#{details.field}` field is redundant"
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{
          message: "Keep one `#{details.field}` section",
          applicability: :manual
        }
      ],
      payload: details
    )
  end

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_packet_name,
             :invalid_packet_endian,
             :unknown_packet_scalar,
             :missing_packet_endian,
             :invalid_packet_field
           ],
      do: packet_failure(kind, %{detail: detail}, opts)

  def from_error({kind, field, dependency}, opts)
      when kind in [:forward_packet_length, :invalid_packet_crc_fields],
      do: packet_failure(kind, %{field: field, dependency: dependency}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_packet_field, :invalid_packet_field_name, :duplicate_packet_field],
      do: packet_failure(kind, %{}, opts)

  def from_error({:invalid_driver_base, base}, opts),
    do: driver_failure(:invalid_driver_base, %{base: base}, opts)

  def from_error(kind, opts)
      when kind in [:invalid_driver_register, :duplicate_driver_register, :overlapping_driver_register],
      do: driver_failure(kind, %{}, opts)

  def from_error({kind, detail}, opts)
      when kind in [
             :invalid_board_name,
             :invalid_board_chip,
             :unknown_board_pin,
             :invalid_board_capability,
             :invalid_board_bus,
             :unknown_bus_pin,
             :missing_bus_capability
           ],
      do: board_failure(kind, %{detail: detail}, opts)

  def from_error(kind, opts)
      when kind in [
             :invalid_board_definition,
             :missing_board_chip,
             :invalid_board_pins,
             :invalid_board_capabilities,
             :invalid_board_buses,
             :invalid_board_flash,
             :flash_offset_out_of_bounds
           ],
      do: board_failure(kind, %{}, opts)

  def from_error({:duplicate_unit, suffix}, opts),
    do: unit_failure(:duplicate_unit, %{suffix: suffix}, opts)

  def from_error({kind, detail}, opts) when kind in [:invalid_unit, :unknown_unit],
    do: unit_failure(kind, %{suffix: detail}, opts)

  def from_error({:invalid_unit_literal, value, suffix}, opts),
    do: unit_failure(:invalid_unit_literal, %{value: value, suffix: suffix}, opts)

  def from_error({:macro_expansion_cycle, frames}, opts)
      when is_list(frames),
      do:
        macro_expansion_failure(
          :cycle,
          "Macro expansion is recursive and did not reach a stable result.",
          frames,
          opts
        )

  def from_error({:macro_expansion_budget, kind, frames}, opts)
      when is_atom(kind) and is_list(frames),
      do:
        macro_expansion_failure(
          {:budget, kind},
          "Macro expansion exceeded its #{kind} limit.",
          frames,
          opts
        )

  def from_error({:expansion_ill_typed, details}, opts)
      when is_map(details) do
    keyword = Map.get(details, :keyword, "computed")

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title: "Macro expansion proof failed",
      body: Doc.paragraph("The `#{keyword}` macro generated code that does not satisfy the dependent elaborator."),
      primary:
        label(
          Keyword.get(opts, :span),
          :primary,
          "this macro invocation generated the invalid expansion"
        ),
      notes: [
        "Edit the authored macro invocation; generated code is an implementation detail."
      ],
      provenance: Keyword.get(opts, :provenance, []),
      payload: %{
        keyword: keyword,
        input: Map.get(details, :input),
        expansion: Map.get(details, :expansion),
        reason:
          inspect(
            Map.get(details, :kernel_error) ||
              Map.get(details, :reason)
          )
      }
    )
  end

  def from_error(error, _opts),
    do: raise(Cure.Diagnostic.UnhandledError, error: error)

  @doc false
  def packet_failure(kind, details, opts) do
    {title, message, label_text, hint} = packet_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_packet_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  @doc false
  def driver_failure(kind, details, opts) do
    {title, message, label_text, hint} = driver_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_driver_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp driver_content(:invalid_driver_base, %{base: base}) do
    {"Driver base address is invalid",
     "A driver base address must be a non-negative integer, but this definition uses `#{name_to_string(base)}`.",
     "replace this base address", "Use the non-negative byte address where this device's register block begins"}
  end

  defp driver_content(:invalid_driver_register, _details) do
    {"Driver register is malformed",
     "Every register needs a name, a non-negative byte offset, an 8-, 16-, or 32-bit width, and `read`, `write`, or `read_write` access.",
     "rewrite this register declaration", "Provide `name`, `offset`, `width`, and `access` for every register"}
  end

  defp driver_content(:duplicate_driver_register, _details) do
    {"Driver register name is repeated", "Two registers have the same name, so generated accessors would collide.",
     "rename or remove this repeated register", "Give every register a unique name"}
  end

  defp driver_content(:overlapping_driver_register, _details) do
    {"Driver register ranges overlap",
     "Two registers occupy at least one of the same bytes in the device register map.",
     "move or resize one of these registers", "Choose offsets and widths whose byte ranges do not overlap"}
  end

  @doc false
  def board_failure(kind, details, opts) do
    {title, message, label_text, hint} = board_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_board_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp board_content(:invalid_board_definition, _details) do
    {"Board definition is malformed",
     "A board definition must be a map containing its chip, pins, capabilities, buses, and flash layout.",
     "rewrite this board definition",
     "Provide a board definition map with `chip`, `pins`, `capabilities`, `buses`, and `flash`"}
  end

  defp board_content(:invalid_board_name, %{detail: name}) do
    {"Board name is invalid",
     "A board name must be an atom or string, but this definition uses `#{name_to_string(name)}`.",
     "replace this board name", "Use a stable board name such as `Esp32c3`"}
  end

  defp board_content(:missing_board_chip, _details) do
    {"Board chip is missing", "The board definition does not identify the chip that owns its pins and peripherals.",
     "add this board's chip", "Add a `chip` entry such as `chip: :esp32c3`"}
  end

  defp board_content(:invalid_board_chip, %{detail: chip}) do
    {"Board chip is invalid",
     "A chip identifier must be an atom or string, but this definition uses `#{name_to_string(chip)}`.",
     "replace this chip identifier", "Use a stable chip identifier such as `esp32c3`"}
  end

  defp board_content(:invalid_board_pins, _details) do
    {"Board pin set is invalid", "Pins must be a non-negative inclusive range or a list of non-negative pin numbers.",
     "fix this pin set", "Use `{first, last}` or a list such as `[0, 1, 2]`"}
  end

  defp board_content(:unknown_board_pin, %{detail: pin}) do
    {"Capability refers to an unknown board pin",
     "Pin `#{name_to_string(pin)}` has capabilities here, but it is not present in the board's pin set.",
     "declare this pin or remove its capabilities",
     "Add pin `#{name_to_string(pin)}` to `pins`, or remove this capability entry"}
  end

  defp board_content(:invalid_board_capability, %{detail: pin}) do
    {"Board pin has an invalid capability",
     "Pin `#{name_to_string(pin)}` has a capability outside the supported GPIO, analog, strapping, USB, and touch set.",
     "fix this pin's capabilities", "Use only `input`, `output`, `adc`, `dac`, `strapping`, `usb`, or `touch`"}
  end

  defp board_content(:invalid_board_capabilities, _details) do
    {"Board capabilities are malformed",
     "Board capabilities must be a map from each pin number to a list of supported capabilities.",
     "rewrite this capability map", "Map each pin to its capabilities, for example pin `8` to `input` and `output`"}
  end

  defp board_content(:invalid_board_bus, %{detail: bus}) do
    {"Board bus wiring is invalid",
     "The `#{name_to_string(bus)}` bus needs an atom name and a map from signal names to pin numbers.",
     "rewrite this bus wiring", "Map each signal to its pin, for example `sda` to `8` and `scl` to `9`"}
  end

  defp board_content(:unknown_bus_pin, %{detail: bus}) do
    {"Board bus uses an unknown pin",
     "The `#{name_to_string(bus)}` bus assigns at least one pin that is not present in the board's pin set.",
     "fix this bus pin assignment", "Assign every `#{name_to_string(bus)}` signal to a pin declared by `pins`"}
  end

  defp board_content(:missing_bus_capability, %{detail: bus}) do
    {"Board bus pin has no capability declaration",
     "The `#{name_to_string(bus)}` bus uses a declared pin whose capabilities are missing, so generated peripheral checks cannot validate it.",
     "declare capabilities for every bus pin", "Add each `#{name_to_string(bus)}` pin to the `capabilities` map"}
  end

  defp board_content(:invalid_board_buses, _details) do
    {"Board bus table is malformed", "Board buses must be a map from bus names to signal-to-pin wiring maps.",
     "rewrite this bus table", "Map each bus name to its signal-to-pin wiring"}
  end

  defp board_content(:invalid_board_flash, _details) do
    {"Board flash layout is malformed",
     "Flash layout needs a positive total size and non-negative application and library offsets.",
     "fix this flash layout", "Provide integer `size`, `app_offset`, and `libs_offset` values"}
  end

  defp board_content(:flash_offset_out_of_bounds, _details) do
    {"Board flash offset is outside the device",
     "The application or library partition starts at or beyond the declared flash size.",
     "move this partition inside flash", "Choose `app_offset` and `libs_offset` values smaller than `size`"}
  end

  @doc false
  def unit_failure(kind, details, opts) do
    {title, message, label_text, hint} = unit_content(kind, details)

    Diagnostic.new(
      code: "E092",
      key: :macro_unit_validation,
      severity: :error,
      title: title,
      body: Doc.paragraph(message),
      primary: label(Keyword.get(opts, :span), :primary, label_text),
      suggestions: [%Suggestion{message: hint, applicability: :manual}],
      payload: Map.put(details, :kind, kind)
    )
  end

  defp unit_content(:duplicate_unit, %{suffix: suffix}) do
    {"Unit suffix is already declared",
     "The `#{name_to_string(suffix)}` suffix is registered more than once, so a literal would have two possible scales.",
     "rename or remove this unit declaration",
     "Keep exactly one declaration for the `#{name_to_string(suffix)}` suffix"}
  end

  defp unit_content(:invalid_unit, %{suffix: suffix}) do
    {"Unit declaration is invalid",
     "The `#{name_to_string(suffix)}` unit needs a text suffix, a positive numeric scale, and an atom naming its dimension.",
     "fix this unit declaration", "Use a positive scale and a stable dimension such as `duration`"}
  end

  defp unit_content(:unknown_unit, %{suffix: suffix}) do
    {"Unit suffix is unknown",
     "The `#{name_to_string(suffix)}` suffix is used by this literal, but no unit with that suffix is registered.",
     "declare this unit or change the suffix", "Register `#{name_to_string(suffix)}` before using it in a literal"}
  end

  defp unit_content(:invalid_unit_literal, %{value: value, suffix: suffix}) do
    {"Unit literal is malformed",
     "A unit literal needs a numeric value and a text suffix, but this one uses value `#{name_to_string(value)}` and suffix `#{name_to_string(suffix)}`.",
     "rewrite this unit literal", "Use a number followed by a registered text suffix"}
  end

  defp packet_content(:invalid_packet_name, %{detail: name}) do
    {"Packet name is invalid",
     "A packet name must be an atom or string, but this declaration uses `#{name_to_string(name)}`.",
     "replace this packet name", "Use a stable packet name such as `Frame`"}
  end

  defp packet_content(:invalid_packet_endian, %{detail: endian}) do
    {"Packet byte order is invalid",
     "`#{name_to_string(endian)}` is not a packet byte order. Multi-byte scalar fields use big-endian (`be`) or little-endian (`le`) order.",
     "choose a supported byte order", "Use `endian: :be` or `endian: :le`"}
  end

  defp packet_content(:unknown_packet_scalar, %{detail: scalar}) do
    {"Packet scalar type is unknown", "`#{name_to_string(scalar)}` is not a fixed-width packet scalar.",
     "replace this scalar type", "Use one of `u8`, `i8`, `u16`, `i16`, `u32`, `i32`, or `byte`"}
  end

  defp packet_content(:missing_packet_endian, %{detail: field}) do
    {"Packet field needs a byte order",
     "The multi-byte `#{name_to_string(field)}` field has no byte order, so its encoded bytes would be ambiguous.",
     "declare this field's byte order", "Set `endian: :be` or `endian: :le` on the packet or this field"}
  end

  defp packet_content(:forward_packet_length, %{field: field, dependency: length_field}) do
    {"Packet length field comes too late",
     "The `#{name_to_string(field)}` field takes its length from `#{name_to_string(length_field)}`, but that length field has not been decoded yet.",
     "move the length field before this payload",
     "Declare `#{name_to_string(length_field)}` before `#{name_to_string(field)}`"}
  end

  defp packet_content(:invalid_packet_crc_fields, %{field: field, dependency: missing}) do
    names = missing |> List.wrap() |> Enum.map_join(", ", &"`#{name_to_string(&1)}`")

    {"Packet checksum references unavailable fields",
     "The `#{name_to_string(field)}` checksum includes #{names}, but those fields have not been decoded before the checksum.",
     "fix this checksum coverage",
     "List only earlier packet fields in `over`, or move the referenced fields before `#{name_to_string(field)}`"}
  end

  defp packet_content(:duplicate_packet_field, _details) do
    {"Packet field name is repeated",
     "Two packet fields have the same name, so generated accessors and layout entries would collide.",
     "rename or remove this repeated field", "Give every packet field a unique name"}
  end

  defp packet_content(:invalid_packet_field_name, _details) do
    {"Packet field has no name", "Every packet field needs a name so later length and checksum fields can refer to it.",
     "add a name to this field", "Add a unique `name` to every packet field"}
  end

  defp packet_content(:invalid_packet_field, _details) do
    {"Packet field is malformed",
     "A packet field must declare a name and one supported shape: constant, scalar, bytes, or checksum.",
     "rewrite this packet field", "Use a `const`, `scalar`, `bytes`, or `crc` field with all required properties"}
  end

  defp macro_expansion_failure(kind, message, frames, opts) do
    frame_maps = Enum.filter(frames, &is_map/1)

    provenance =
      Enum.map(frame_maps, fn frame ->
        %ProvenanceFrame{
          kind: :macro_expansion,
          name: Map.get(frame, :keyword, "macro"),
          invocation: Map.get(frame, :invocation),
          definition: Map.get(frame, :definition),
          parent: Map.get(frame, :parent)
        }
      end)

    invocation_spans =
      frame_maps
      |> Enum.map(&Map.get(&1, :invocation))
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    primary_span =
      List.last(invocation_spans) || Keyword.get(opts, :span)

    secondary =
      invocation_spans
      |> Enum.reject(&(&1 == primary_span))
      |> Enum.map(
        &label(
          &1,
          :secondary,
          "this earlier invocation is in the expansion chain"
        )
      )

    suggestion =
      case kind do
        :cycle ->
          "Make recursive macro expansion consume input or terminate before invoking itself again"

        {:budget, _limit} ->
          "Reduce the generated expansion depth or split this macro into smaller steps"
      end

    chain =
      frame_maps
      |> Enum.map(&Map.get(&1, :keyword))
      |> Enum.reject(&is_nil/1)

    Diagnostic.new(
      code: "E092",
      key: :macro_expansion_failed,
      severity: :error,
      title:
        if(kind == :cycle,
          do: "Macro expansion cycle",
          else: "Macro expansion limit exceeded"
        ),
      body: Doc.paragraph(message),
      primary:
        label(
          primary_span,
          :primary,
          if(kind == :cycle,
            do: "this invocation closes the expansion cycle",
            else: "the expansion limit is reached here"
          )
        ),
      secondary: secondary,
      suggestions: [
        %Suggestion{message: suggestion, applicability: :manual}
      ],
      provenance: provenance ++ Keyword.get(opts, :provenance, []),
      payload: %{kind: kind, frames: frames, chain: chain}
    )
  end

  defp syntax_family_field_suggestions(
         %{field: field, valid_fields: fields},
         %Span{} = span
       )
       when is_list(fields),
       do:
         ranked_repair(
           field,
           fields,
           span,
           fn candidate -> "Replace it with `#{candidate}`" end,
           fn candidates ->
             "Use one of: #{Enum.map_join(candidates, ", ", fn field -> "`#{field}`" end)}"
           end
         )

  defp syntax_family_field_suggestions(_details, _span), do: []

  defp macro_capture_suggestions(
         %{capture: capture, available_captures: captures},
         %Span{} = span
       )
       when is_list(captures),
       do:
         ranked_repair(
           capture,
           captures,
           span,
           fn candidate ->
             "Replace it with the declared capture `#{candidate}`"
           end,
           fn candidates ->
             "Refer to one of this rule's captures: #{Enum.map_join(candidates, ", ", fn capture -> "`#{capture}`" end)}"
           end
         )

  defp macro_capture_suggestions(_details, _span), do: []

  defp ranked_repair(spelling, candidates, span, unique_message, fallback_message) do
    spelling = to_string(spelling)

    ranked =
      candidates
      |> Enum.map(&{to_string(&1), Suggest.distance(spelling, to_string(&1))})
      |> Enum.sort_by(fn {candidate, distance} ->
        {distance, String.downcase(candidate), candidate}
      end)

    case ranked do
      [{candidate, distance}, {_other, next_distance} | _]
      when distance <= 2 and distance < next_distance ->
        [replacement(candidate, span, unique_message)]

      [{candidate, distance}] when distance <= 2 ->
        [replacement(candidate, span, unique_message)]

      _ ->
        [
          %Suggestion{
            message: fallback_message.(candidates),
            applicability: :manual
          }
        ]
    end
  end

  defp replacement(candidate, span, message) do
    %Suggestion{
      message: message.(candidate),
      applicability: :machine_applicable,
      edits: [%TextEdit{span: span, replacement: candidate}]
    }
  end

  defp name_to_string(name) when is_atom(name), do: Atom.to_string(name)
  defp name_to_string(name) when is_binary(name), do: name
  defp name_to_string(name), do: inspect(name)

  defp label(%Span{} = span, style, message),
    do: %Label{span: span, style: style, message: message}

  defp label(_span, _style, _message), do: nil
end

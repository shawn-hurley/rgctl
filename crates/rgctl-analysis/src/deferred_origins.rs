//! Bounded possible-value models for explicit deferred handoffs.
use super::*;
impl<C: InterproceduralCfgAccess + ?Sized> Query<'_, C> {
    pub(super) fn register_deferred(&mut self, function: Uuid) {
        let Some(cfg) = self.icfg.get_cfg(function) else {
            return;
        };
        for (index, site) in cfg.operands.calls.iter().enumerate() {
            if !self.step() {
                break;
            }
            let call = CallRef {
                caller: function,
                site: CallSiteId(index as u32),
            };
            let arguments = site.arguments.slice(&cfg.operands.arguments).unwrap_or(&[]);
            let Some(first) = arguments.first() else {
                continue;
            };
            let result = ValueRef {
                function,
                expression: site.result,
            };
            let value = ValueRef {
                function,
                expression: first.value,
            };
            let callee = &cfg.operands.expressions[site.callee.0 as usize];
            let name = match callee.kind {
                ExpressionKind::Name(n) | ExpressionKind::Member(n) => cfg.operands.name(n),
                _ => None,
            };
            if cfg.operands.language == OperandLanguage::Python
                && name == Some("next")
                && matches!(callee.kind, ExpressionKind::Name(_))
            {
                self.memory_access(value, MemoryMember::Element, result, false);
            }
            if cfg.operands.language==OperandLanguage::Python && name==Some("run")
                && site.receiver.is_some_and(|receiver| matches!(cfg.operands.expressions[receiver.0 as usize].kind,ExpressionKind::Name(n) if cfg.operands.name(n)==Some("asyncio"))) {
                self.edge(value,result,OriginTransferCause::DeferredCall{call});
            }
            if cfg.operands.language == OperandLanguage::Go
                && name == Some("make")
                && cfg.operands.expressions[first.value.0 as usize].kind
                    == ExpressionKind::ChannelType
            {
                self.seed(OriginSeed {
                    value: result,
                    type_id: None,
                });
            }
        }
    }
    pub(super) fn bind_yields(&mut self, target: InvocationTarget) {
        let Some(callee) = self.icfg.get_cfg(target.callee) else {
            return;
        };
        if callee.operands.yields.is_empty() {
            return;
        }
        let Some(caller) = self.icfg.get_cfg(target.call.caller) else {
            return;
        };
        let Some(site) = caller.operands.calls.get(target.call.site.0 as usize) else {
            return;
        };
        let result = ValueRef {
            function: target.call.caller,
            expression: site.result,
        };
        self.seed(OriginSeed {
            value: result,
            type_id: None,
        });
        for &value in &callee.operands.yields {
            if !self.step() {
                break;
            }
            self.memory_access(
                result,
                MemoryMember::Element,
                ValueRef {
                    function: target.callee,
                    expression: value,
                },
                true,
            );
        }
    }
}
